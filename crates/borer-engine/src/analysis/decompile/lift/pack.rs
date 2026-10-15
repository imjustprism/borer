//! A function's effects packed into bytes, as the memo keeps them.
//!
//! An [`Effect`] holds its values as expression trees, every node a box of
//! its own: about four hundred bytes a statement, eight times the text it
//! stands beside, which a memo of decompilations held in full would spend
//! its budget on. Packed, a node is a tag byte and a varint or two, a
//! statement about a tenth of its line. A block's effects unpack on
//! demand, as the values they were.

use crate::isa::x86::{ConditionCode, Register};

use super::super::expr::{Cc, Cond, Expr, Flags, Key, Op, Ty, UnOp, a64_code, a64_reg};
use super::{ArgAt, Call, Callee, Effect, EffectKind, Routine, Shown};

/// The routines a [`Callee::Builtin`] names, by packed code.
const ROUTINES: [Routine; 3] = [Routine::Memset, Routine::Memcpy, Routine::Memmove];

/// Every block's effects of one function, packed one block after another.
#[derive(Debug, Default)]
pub(in crate::analysis::decompile) struct Packed {
    /// The packed effects of every block, in block order.
    bytes: Box<[u8]>,
    /// Where each block's effects end in `bytes`, by block index.
    ends: Box<[usize]>,
}

impl Packed {
    /// Joins blocks' packed effects, in block order.
    ///
    /// # Arguments
    ///
    /// * `blocks` - Each block's packed effects ([`pack`]); empty for a
    ///   block with none.
    pub(in crate::analysis::decompile) fn new(blocks: impl Iterator<Item = Vec<u8>>) -> Self {
        let mut bytes = Vec::new();
        let mut ends = Vec::new();
        for b in blocks {
            bytes.extend_from_slice(&b);
            ends.push(bytes.len());
        }
        Self {
            bytes: bytes.into_boxed_slice(),
            ends: ends.into_boxed_slice(),
        }
    }

    /// The bytes held, which the memo keeping them counts.
    pub(in crate::analysis::decompile) fn bytes(&self) -> usize {
        self.bytes.len() + self.ends.len() * size_of::<usize>()
    }

    /// Unpacks one block's effects.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `start` - The block's start, which the effects' addresses count from.
    ///
    /// # Returns
    ///
    /// The effects in the order the text makes them, or `None` when there
    /// is no such block.
    pub(in crate::analysis::decompile) fn block(
        &self,
        b: usize,
        start: u64,
    ) -> Option<Vec<Effect>> {
        let from = b
            .checked_sub(1)
            .map_or(Some(0), |p| self.ends.get(p).copied())?;
        let to = *self.ends.get(b)?;
        let mut r = Reader {
            bytes: self.bytes.get(from..to)?,
            at: start,
        };
        let mut out = Vec::new();
        while !r.bytes.is_empty() {
            out.push(r.effect()?);
        }
        Some(out)
    }
}

/// Packs a block's effects, appending them to `out`.
///
/// # Arguments
///
/// * `effects` - The effects, in order.
/// * `start` - The block's start: each effect's address is packed as its
///   distance from the one before, the first from this.
/// * `out` - Where the bytes go.
pub(in crate::analysis::decompile) fn pack(effects: &[Effect], start: u64, out: &mut Vec<u8>) {
    let mut w = Writer { out, at: start };
    for e in effects {
        w.effect(e);
    }
}

/// The packed code of a type.
///
/// # Arguments
///
/// * `ty` - The type.
fn ty_code(ty: Ty) -> u8 {
    match ty {
        Ty::U8 => 0,
        Ty::U16 => 1,
        Ty::U32 => 2,
        Ty::U64 => 3,
        Ty::U128 => 4,
        Ty::F32 => 5,
        Ty::F64 => 6,
    }
}

/// The types by packed code.
const TYS: [Ty; 7] = [
    Ty::U8,
    Ty::U16,
    Ty::U32,
    Ty::U64,
    Ty::U128,
    Ty::F32,
    Ty::F64,
];

/// The packed code of a binary operator and its width operand.
///
/// # Arguments
///
/// * `op` - The operator.
fn op_code(op: Op) -> (u8, Option<u8>) {
    match op {
        Op::Add => (0, None),
        Op::Sub => (1, None),
        Op::Mul => (2, None),
        Op::Div => (3, None),
        Op::Rem => (4, None),
        Op::SDiv => (5, None),
        Op::SRem => (6, None),
        Op::And => (7, None),
        Op::Or => (8, None),
        Op::Xor => (9, None),
        Op::Shl => (10, None),
        Op::Shr => (11, None),
        Op::Sar => (12, None),
        Op::Rol(w) => (13, Some(w)),
        Op::Ror(w) => (14, Some(w)),
        Op::MulHi(w) => (15, Some(w)),
        Op::SMulHi(w) => (16, Some(w)),
        Op::SMulO(w) => (17, Some(w)),
        Op::UAddO(w) => (18, Some(w)),
        Op::USubO(w) => (19, Some(w)),
        Op::FAdd => (20, None),
        Op::FSub => (21, None),
        Op::FMul => (22, None),
        Op::FDiv => (23, None),
        Op::FMin => (24, None),
        Op::FMax => (25, None),
    }
}

/// The binary operator a packed code names.
///
/// # Arguments
///
/// * `code` - The code.
/// * `w` - Its width operand, read only for the operators that take one.
fn op_of(code: u8, w: impl FnOnce() -> Option<u8>) -> Option<Op> {
    Some(match code {
        0 => Op::Add,
        1 => Op::Sub,
        2 => Op::Mul,
        3 => Op::Div,
        4 => Op::Rem,
        5 => Op::SDiv,
        6 => Op::SRem,
        7 => Op::And,
        8 => Op::Or,
        9 => Op::Xor,
        10 => Op::Shl,
        11 => Op::Shr,
        12 => Op::Sar,
        13 => Op::Rol(w()?),
        14 => Op::Ror(w()?),
        15 => Op::MulHi(w()?),
        16 => Op::SMulHi(w()?),
        17 => Op::SMulO(w()?),
        18 => Op::UAddO(w()?),
        19 => Op::USubO(w()?),
        20 => Op::FAdd,
        21 => Op::FSub,
        22 => Op::FMul,
        23 => Op::FDiv,
        24 => Op::FMin,
        25 => Op::FMax,
        _ => return None,
    })
}

/// The packed code of a unary operator.
///
/// # Arguments
///
/// * `op` - The operator.
fn unop_code(op: UnOp) -> u8 {
    match op {
        UnOp::Neg => 0,
        UnOp::Not => 1,
        UnOp::Bswap => 2,
        UnOp::Tzcnt => 3,
        UnOp::Lzcnt => 4,
        UnOp::Popcnt => 5,
        UnOp::Sqrt => 6,
        UnOp::Fabs => 7,
        UnOp::Bsf => 8,
        UnOp::Bsr => 9,
    }
}

/// The unary operators by packed code.
const UNOPS: [UnOp; 10] = [
    UnOp::Neg,
    UnOp::Not,
    UnOp::Bswap,
    UnOp::Tzcnt,
    UnOp::Lzcnt,
    UnOp::Popcnt,
    UnOp::Sqrt,
    UnOp::Fabs,
    UnOp::Bsf,
    UnOp::Bsr,
];

/// The packed code of how a call shows.
///
/// # Arguments
///
/// * `shown` - How it shows.
fn shown_code(shown: Shown) -> u8 {
    match shown {
        Shown::Statement => 0,
        Shown::Tail => 1,
        Shown::Elided => 2,
        Shown::InPlace => 3,
    }
}

/// How a call shows, by packed code.
const SHOWNS: [Shown; 4] = [Shown::Statement, Shown::Tail, Shown::Elided, Shown::InPlace];

/// Writes effects as bytes.
struct Writer<'o> {
    /// Where the bytes go.
    out: &'o mut Vec<u8>,
    /// The address of the effect before, which the next one's counts from.
    at: u64,
}

impl Writer<'_> {
    /// Writes a byte.
    ///
    /// # Arguments
    ///
    /// * `b` - The byte.
    fn byte(&mut self, b: u8) {
        self.out.push(b);
    }

    /// Writes an unsigned number in seven-bit groups, low first, the top
    /// bit of each saying another follows.
    ///
    /// # Arguments
    ///
    /// * `v` - The number.
    fn num(&mut self, mut v: u64) {
        while v >= 0x80 {
            self.out.push(crate::num::lo8(v) | 0x80);
            v >>= 7;
        }
        self.out.push(crate::num::lo8(v));
    }

    /// Writes a signed number, folded so small magnitudes of either sign
    /// take one byte.
    ///
    /// # Arguments
    ///
    /// * `v` - The number.
    fn signed(&mut self, v: i64) {
        self.num(((v << 1) ^ (v >> 63)).cast_unsigned());
    }

    /// Writes a string: its length, then its bytes.
    ///
    /// # Arguments
    ///
    /// * `s` - The string.
    fn text(&mut self, s: &str) {
        self.num(crate::num::from_usize(s.len()));
        self.out.extend_from_slice(s.as_bytes());
    }

    /// Writes a register.
    ///
    /// # Arguments
    ///
    /// * `r` - The register.
    fn reg(&mut self, r: Register) {
        self.num(crate::num::from_usize(r as usize));
    }

    /// Writes a text variable.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    fn key(&mut self, k: Key) {
        match k {
            Key::Reg(r) => {
                self.byte(0);
                self.reg(r);
            }
            Key::Slot(o) => {
                self.byte(1);
                self.signed(o);
            }
            Key::Global(a, bits) => {
                self.byte(2);
                self.num(a);
                self.byte(bits);
            }
            Key::Tmp(id) => {
                self.byte(3);
                self.num(u64::from(id));
            }
            Key::Param(i) => {
                self.byte(4);
                self.byte(i);
            }
            Key::A64(r) => {
                self.byte(5);
                self.byte(a64_code(r));
            }
        }
    }

    /// Writes an expression, its operands after it.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    fn expr(&mut self, e: &Expr) {
        match e {
            Expr::Const(v) => {
                self.byte(0);
                self.num(*v);
            }
            Expr::Var(k) => {
                self.byte(1);
                self.key(*k);
            }
            Expr::Str(s) => {
                self.byte(2);
                self.text(s);
            }
            Expr::Sp(o) => {
                self.byte(3);
                self.signed(*o);
            }
            Expr::Bin(op, l, r) => {
                self.byte(4);
                let (code, w) = op_code(*op);
                self.byte(code);
                if let Some(w) = w {
                    self.byte(w);
                }
                self.expr(l);
                self.expr(r);
            }
            Expr::Un(op, x) => {
                self.byte(5);
                self.byte(unop_code(*op));
                self.expr(x);
            }
            Expr::Deref(a, ty) => {
                self.byte(6);
                self.byte(ty_code(*ty));
                self.expr(a);
            }
            Expr::Cond(c) => {
                self.byte(7);
                self.cond(c);
            }
            Expr::Ternary(c, a, b) => {
                self.byte(8);
                self.cond(c);
                self.expr(a);
                self.expr(b);
            }
            Expr::Sext(x, bits) => {
                self.byte(9);
                self.byte(*bits);
                self.expr(x);
            }
            Expr::Cast(x, ty) => {
                self.byte(10);
                self.byte(ty_code(*ty));
                self.expr(x);
            }
            Expr::Call(name, args) => {
                self.byte(11);
                self.text(name);
                self.num(crate::num::from_usize(args.len()));
                for a in args {
                    self.expr(a);
                }
            }
            Expr::FConst(bits, ty) => {
                self.byte(12);
                self.byte(ty_code(*ty));
                self.num(*bits);
            }
        }
    }

    /// Writes a condition: its code, then what set the flags.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    fn cond(&mut self, c: &Cond) {
        self.num(crate::num::from_usize(c.cc.0 as usize));
        match &c.flags {
            Flags::Cmp(a, b, w) => self.pair(0, *w, a, b),
            Flags::Float(a, b, w) => self.pair(8, *w, a, b),
            Flags::Test(a, b, w) => self.pair(1, *w, a, b),
            Flags::Add(a, b, w) => self.pair(3, *w, a, b),
            Flags::Result(a, w) => {
                self.byte(2);
                self.byte(*w);
                self.expr(a);
            }
            Flags::Carry(a) => {
                self.byte(4);
                self.expr(a);
            }
            Flags::Shift(a, w, b) => {
                self.byte(5);
                self.byte(*w);
                self.expr(a);
                self.expr(b);
            }
            Flags::Truth(a, cc) => {
                self.byte(6);
                self.num(crate::num::from_usize(cc.0 as usize));
                self.expr(a);
            }
            Flags::Unknown => self.byte(7),
        }
    }

    /// Writes flags set from two operands at a width.
    ///
    /// # Arguments
    ///
    /// * `code` - Which flags.
    /// * `w` - The width.
    /// * `a` - The left operand.
    /// * `b` - The right operand.
    fn pair(&mut self, code: u8, w: u8, a: &Expr, b: &Expr) {
        self.byte(code);
        self.byte(w);
        self.expr(a);
        self.expr(b);
    }

    /// Writes an expression that may be absent.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression, if any.
    fn maybe(&mut self, e: Option<&Expr>) {
        match e {
            Some(e) => {
                self.byte(1);
                self.expr(e);
            }
            None => self.byte(0),
        }
    }

    /// Writes a call.
    ///
    /// # Arguments
    ///
    /// * `c` - The call.
    fn call(&mut self, c: &Call) {
        match &c.callee {
            Callee::Direct(t) => {
                self.byte(0);
                self.num(*t);
            }
            Callee::Through(e) => {
                self.byte(1);
                self.expr(e);
            }
            Callee::Builtin(routine, bits) => {
                self.byte(2);
                self.byte(match routine {
                    Routine::Memset => 0,
                    Routine::Memcpy => 1,
                    Routine::Memmove => 2,
                });
                self.byte(*bits);
            }
        }
        self.num(crate::num::from_usize(c.args.len()));
        for (at, e) in &c.args {
            match at {
                ArgAt::Reg(r) => {
                    self.byte(0);
                    self.reg(*r);
                }
                ArgAt::Stack(o, bits) => {
                    self.byte(1);
                    self.signed(*o);
                    self.byte(*bits);
                }
                ArgAt::Operand => self.byte(2),
                ArgAt::A64(r) => {
                    self.byte(3);
                    self.byte(a64_code(*r));
                }
            }
            self.expr(e);
        }
        match c.result {
            Some(k) => {
                self.byte(1);
                self.key(k);
            }
            None => self.byte(0),
        }
        match c.result2 {
            Some(k) => {
                self.byte(1);
                self.key(k);
            }
            None => self.byte(0),
        }
        self.byte(
            u8::from(c.noreturn)
                | (shown_code(c.shown) << 1)
                | (u8::from(c.short) << 3)
                | (u8::from(c.contradicted) << 4),
        );
    }

    /// Writes an effect: its distance from the one before, then what it does.
    ///
    /// # Arguments
    ///
    /// * `e` - The effect.
    fn effect(&mut self, e: &Effect) {
        self.signed(e.at.wrapping_sub(self.at).cast_signed());
        self.at = e.at;
        match &e.kind {
            EffectKind::Assign(k, v, bits) => {
                self.byte(0);
                self.key(*k);
                self.byte(*bits);
                self.expr(v);
            }
            EffectKind::Store(s) => {
                self.byte(1);
                self.byte(ty_code(s.1));
                self.expr(&s.0);
                self.expr(&s.2);
            }
            EffectKind::Call(c) => {
                self.byte(2);
                self.call(c);
            }
            EffectKind::Return(v) => {
                self.byte(3);
                self.maybe(v.as_ref());
            }
            EffectKind::Branch(c) => {
                self.byte(4);
                self.cond(c);
            }
            EffectKind::Switch(e) => {
                self.byte(5);
                self.expr(e);
            }
            EffectKind::Jump(e) => {
                self.byte(6);
                self.expr(e);
            }
            EffectKind::Unmodeled => self.byte(7),
        }
    }
}

/// Reads effects back from bytes; every read is `None` past the end or at
/// a code nothing packs.
struct Reader<'b> {
    /// The bytes not read yet.
    bytes: &'b [u8],
    /// The address of the effect before, which the next one's counts from.
    at: u64,
}

impl Reader<'_> {
    /// Reads a byte.
    fn byte(&mut self) -> Option<u8> {
        let (&b, rest) = self.bytes.split_first()?;
        self.bytes = rest;
        Some(b)
    }

    /// Reads an unsigned number ([`Writer::num`]).
    fn num(&mut self) -> Option<u64> {
        let mut v = 0u64;
        for shift in (0..64).step_by(7) {
            let b = self.byte()?;
            v |= u64::from(b & 0x7f).checked_shl(shift)?;
            if b & 0x80 == 0 {
                return Some(v);
            }
        }
        None
    }

    /// Reads a signed number ([`Writer::signed`]).
    fn signed(&mut self) -> Option<i64> {
        let v = self.num()?;
        Some((v >> 1).cast_signed() ^ (v & 1).cast_signed().wrapping_neg())
    }

    /// Reads a count or a length.
    fn len(&mut self) -> Option<usize> {
        usize::try_from(self.num()?).ok()
    }

    /// Reads a string.
    fn text(&mut self) -> Option<String> {
        let n = self.len()?;
        let s = self.bytes.get(..n)?;
        self.bytes = self.bytes.get(n..)?;
        String::from_utf8(s.to_vec()).ok()
    }

    /// Reads a register.
    fn reg(&mut self) -> Option<Register> {
        Register::try_from(self.len()?).ok()
    }

    /// Reads a type.
    fn ty(&mut self) -> Option<Ty> {
        TYS.get(usize::from(self.byte()?)).copied()
    }

    /// Reads a condition code.
    fn cc(&mut self) -> Option<Cc> {
        ConditionCode::try_from(self.len()?).ok().map(Cc)
    }

    /// Reads a text variable.
    fn key(&mut self) -> Option<Key> {
        Some(match self.byte()? {
            0 => Key::Reg(self.reg()?),
            1 => Key::Slot(self.signed()?),
            2 => {
                let a = self.num()?;
                Key::Global(a, self.byte()?)
            }
            3 => Key::Tmp(u32::try_from(self.num()?).ok()?),
            4 => Key::Param(self.byte()?),
            5 => Key::A64(a64_reg(self.byte()?)?),
            _ => return None,
        })
    }

    /// Reads a boxed expression.
    fn boxed(&mut self) -> Option<Box<Expr>> {
        self.expr().map(Box::new)
    }

    /// Reads an expression.
    fn expr(&mut self) -> Option<Expr> {
        Some(match self.byte()? {
            0 => Expr::Const(self.num()?),
            1 => Expr::Var(self.key()?),
            2 => Expr::Str(self.text()?),
            3 => Expr::Sp(self.signed()?),
            4 => {
                let code = self.byte()?;
                let op = op_of(code, || self.byte())?;
                let l = self.boxed()?;
                Expr::Bin(op, l, self.boxed()?)
            }
            5 => {
                let op = *UNOPS.get(usize::from(self.byte()?))?;
                Expr::Un(op, self.boxed()?)
            }
            6 => {
                let ty = self.ty()?;
                Expr::Deref(self.boxed()?, ty)
            }
            7 => Expr::Cond(Box::new(self.cond()?)),
            8 => {
                let c = Box::new(self.cond()?);
                let a = self.boxed()?;
                Expr::Ternary(c, a, self.boxed()?)
            }
            9 => {
                let bits = self.byte()?;
                Expr::Sext(self.boxed()?, bits)
            }
            10 => {
                let ty = self.ty()?;
                Expr::Cast(self.boxed()?, ty)
            }
            11 => {
                let name = self.text()?;
                let n = self.len()?;
                let args = (0..n).map(|_| self.expr()).collect::<Option<Vec<_>>>()?;
                Expr::Call(name, args)
            }
            12 => {
                let ty = self.ty()?;
                Expr::FConst(self.num()?, ty)
            }
            _ => return None,
        })
    }

    /// Reads a condition.
    fn cond(&mut self) -> Option<Cond> {
        let cc = self.cc()?;
        let flags = match self.byte()? {
            code @ (0 | 1 | 3 | 8) => {
                let w = self.byte()?;
                let a = self.expr()?;
                let b = self.expr()?;
                match code {
                    0 => Flags::Cmp(a, b, w),
                    1 => Flags::Test(a, b, w),
                    8 => Flags::Float(a, b, w),
                    _ => Flags::Add(a, b, w),
                }
            }
            2 => {
                let w = self.byte()?;
                Flags::Result(self.expr()?, w)
            }
            4 => Flags::Carry(self.expr()?),
            5 => {
                let w = self.byte()?;
                let a = self.expr()?;
                Flags::Shift(a, w, self.expr()?)
            }
            6 => {
                let truth = self.cc()?;
                Flags::Truth(self.expr()?, truth)
            }
            7 => Flags::Unknown,
            _ => return None,
        };
        Some(Cond { cc, flags })
    }

    /// Reads an expression that may be absent.
    fn maybe(&mut self) -> Option<Option<Expr>> {
        match self.byte()? {
            0 => Some(None),
            1 => Some(Some(self.expr()?)),
            _ => None,
        }
    }

    /// Reads a call.
    fn call(&mut self) -> Option<Call> {
        let callee = match self.byte()? {
            0 => Callee::Direct(self.num()?),
            1 => Callee::Through(self.expr()?),
            2 => {
                let routine = *ROUTINES.get(usize::from(self.byte()?))?;
                Callee::Builtin(routine, self.byte()?)
            }
            _ => return None,
        };
        let n = self.len()?;
        let mut args = Vec::new();
        for _ in 0..n {
            let at = match self.byte()? {
                0 => ArgAt::Reg(self.reg()?),
                1 => {
                    let o = self.signed()?;
                    ArgAt::Stack(o, self.byte()?)
                }
                2 => ArgAt::Operand,
                3 => ArgAt::A64(a64_reg(self.byte()?)?),
                _ => return None,
            };
            args.push((at, self.expr()?));
        }
        let result = match self.byte()? {
            0 => None,
            1 => Some(self.key()?),
            _ => return None,
        };
        let result2 = match self.byte()? {
            0 => None,
            1 => Some(self.key()?),
            _ => return None,
        };
        let bits = self.byte()?;
        Some(Call {
            callee,
            args,
            result,
            result2,
            noreturn: bits & 1 != 0,
            shown: *SHOWNS.get(usize::from((bits >> 1) & 3))?,
            short: bits & 8 != 0,
            contradicted: bits & 16 != 0,
        })
    }

    /// Reads an effect.
    fn effect(&mut self) -> Option<Effect> {
        let at = self.at.wrapping_add_signed(self.signed()?);
        self.at = at;
        let kind = match self.byte()? {
            0 => {
                let k = self.key()?;
                let bits = self.byte()?;
                EffectKind::Assign(k, self.expr()?, bits)
            }
            1 => {
                let ty = self.ty()?;
                let addr = self.expr()?;
                EffectKind::Store(Box::new((addr, ty, self.expr()?)))
            }
            2 => EffectKind::Call(Box::new(self.call()?)),
            3 => EffectKind::Return(self.maybe()?),
            4 => EffectKind::Branch(self.cond()?),
            5 => EffectKind::Switch(self.expr()?),
            6 => EffectKind::Jump(self.expr()?),
            7 => EffectKind::Unmodeled,
            _ => return None,
        };
        Some(Effect { at, kind })
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use crate::isa::x86::{ConditionCode, Register};

    use super::{
        Packed, ROUTINES, SHOWNS, TYS, UNOPS, op_code, op_of, pack, shown_code, ty_code, unop_code,
    };
    use crate::analysis::decompile::expr::{Cc, Cond, Expr, Flags, Key, Op, Ty, UnOp};
    use crate::analysis::decompile::lift::{
        ArgAt, Call, Callee, Effect, EffectKind, Routine, Shown,
    };

    /// Every code a type, an operator or a call's showing packs to reads
    /// back as itself.
    #[test]
    fn every_code_reads_back() {
        for ty in TYS {
            assert_eq!(TYS[usize::from(ty_code(ty))], ty);
        }
        for op in UNOPS {
            assert_eq!(UNOPS[usize::from(unop_code(op))], op);
        }
        for shown in SHOWNS {
            assert_eq!(SHOWNS[usize::from(shown_code(shown))], shown);
        }
        let ops = [
            Op::Add,
            Op::Sub,
            Op::Mul,
            Op::Div,
            Op::Rem,
            Op::SDiv,
            Op::SRem,
            Op::And,
            Op::Or,
            Op::Xor,
            Op::Shl,
            Op::Shr,
            Op::Sar,
            Op::Rol(8),
            Op::Ror(16),
            Op::MulHi(32),
            Op::SMulHi(64),
            Op::SMulO(32),
            Op::UAddO(8),
            Op::USubO(16),
            Op::FAdd,
            Op::FSub,
            Op::FMul,
            Op::FDiv,
            Op::FMin,
            Op::FMax,
        ];
        for op in ops {
            let (code, w) = op_code(op);
            assert_eq!(op_of(code, || w), Some(op));
        }
        assert_eq!(ROUTINES.len(), 3);
    }

    /// A block's effects of every kind, packed beside another block's,
    /// unpack as they were, and take a fraction of the bytes they held.
    #[test]
    fn effects_unpack_as_they_were() {
        let var = |r| Expr::Var(Key::Reg(r));
        let load = Expr::Deref(
            Box::new(Expr::Bin(
                Op::Add,
                Box::new(var(Register::RCX)),
                Box::new(Expr::Const(8)),
            )),
            Ty::U64,
        );
        let cond = Cond {
            cc: Cc(ConditionCode::l),
            flags: Flags::Cmp(load.clone(), Expr::Const(u64::MAX), 32),
        };
        let effects = vec![
            Effect {
                at: 0x1000,
                kind: EffectKind::Assign(Key::Slot(-0x18), load, 32),
            },
            Effect {
                at: 0x1004,
                kind: EffectKind::Store(Box::new((
                    Expr::Var(Key::Global(0x4000, 32)),
                    Ty::F32,
                    Expr::FConst(0x3f80_0000, Ty::F32),
                ))),
            },
            Effect {
                at: 0x1008,
                kind: EffectKind::Call(Box::new(Call {
                    callee: Callee::Through(Expr::Un(UnOp::Not, Box::new(var(Register::RAX)))),
                    args: vec![
                        (ArgAt::Reg(Register::RCX), Expr::Str("a \"b\"".to_owned())),
                        (ArgAt::Stack(0x28, 16), Expr::Sp(-0x40)),
                        (
                            ArgAt::Operand,
                            Expr::Call("x".to_owned(), vec![Expr::Var(Key::Tmp(3))]),
                        ),
                    ],
                    result: Some(Key::Reg(Register::RAX)),
                    result2: None,
                    noreturn: true,
                    shown: Shown::InPlace,
                    short: true,
                    contradicted: true,
                })),
            },
            Effect {
                at: 0x1002,
                kind: EffectKind::Return(Some(Expr::Ternary(
                    Box::new(cond.clone()),
                    Box::new(Expr::Sext(Box::new(var(Register::RDX)), 16)),
                    Box::new(Expr::Cast(Box::new(Expr::Var(Key::Param(2))), Ty::U8)),
                ))),
            },
            Effect {
                at: 0x100c,
                kind: EffectKind::Branch(Cond {
                    cc: Cc(ConditionCode::ne),
                    flags: Flags::Truth(Expr::Cond(Box::new(cond)), Cc(ConditionCode::e)),
                }),
            },
            Effect {
                at: 0x100c,
                kind: EffectKind::Call(Box::new(Call {
                    callee: Callee::Builtin(Routine::Memmove, 8),
                    args: Vec::new(),
                    result: None,
                    result2: None,
                    noreturn: false,
                    shown: Shown::Tail,
                    short: false,
                    contradicted: false,
                })),
            },
            Effect {
                at: 0x100c,
                kind: EffectKind::Return(None),
            },
            Effect {
                at: 0x100e,
                kind: EffectKind::Switch(var(Register::R9)),
            },
            Effect {
                at: 0x100e,
                kind: EffectKind::Jump(Expr::Const(0x2000)),
            },
            Effect {
                at: 0x100e,
                kind: EffectKind::Unmodeled,
            },
        ];
        let other = vec![Effect {
            at: 0x3000,
            kind: EffectKind::Call(Box::new(Call {
                callee: Callee::Direct(0x5000),
                args: Vec::new(),
                result: None,
                result2: None,
                noreturn: false,
                shown: Shown::Elided,
                short: false,
                contradicted: false,
            })),
        }];
        let (mut first, mut second) = (Vec::new(), Vec::new());
        pack(&effects, 0x1000, &mut first);
        pack(&other, 0x3000, &mut second);
        let held = size_of::<Effect>() * effects.len();
        assert!(first.len() * 4 < held, "{} bytes", first.len());
        let packed = Packed::new([first, Vec::new(), second].into_iter());
        assert_eq!(packed.block(0, 0x1000), Some(effects));
        assert_eq!(packed.block(1, 0x2000), Some(Vec::new()));
        assert_eq!(packed.block(2, 0x3000), Some(other));
        assert_eq!(packed.block(3, 0x4000), None);
    }
}
