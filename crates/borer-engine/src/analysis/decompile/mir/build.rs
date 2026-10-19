//! Lowering the lifter's expressions ([`Expr`], [`Cond`]) to MIR.
//!
//! An expression holds no width on its operators: every integer operator
//! computes at the machine word, and a float operation takes its width
//! from the types its operands carry. The lowering states both. Each
//! integer operator becomes an op at the word over operands cut or
//! extended to it, each float operation a float op of the type its
//! operands' types give, and each condition a compare at the width its
//! flags were set at. What an expression leaves to its reader (a float
//! operation over operands of no float type, an operator of no recorded
//! width) is an [`Inst::Undef`], so the MIR says exactly what the
//! expression evaluator can read, and no more.

use std::collections::BTreeMap;

use crate::isa::x86::ConditionCode;

use super::super::expr::{
    Cc, Cond, Expr, Flags, Key, Op, Ty, UnOp as EUn, fcvt_float_width, tls_slot,
};
use super::super::fcmp::FPred;
use super::super::helper::{Helper, Operands, arg_bits};
use super::super::verify::EVAL_DEPTH;
use super::{
    BinOp, Body, FOp, FUnOp, Hole, IPred, Inst, Lane, MTy, OvfOp, Prov, UnOp, Val, WideOp,
};

/// Builds one body from the lifter's expressions.
pub(in super::super) struct Builder<'a> {
    /// The body built so far.
    pub(in super::super) body: Body,
    /// The temporaries the lifter made, by id, with the value each copied.
    temps: &'a BTreeMap<u32, Expr>,
    /// The provenance every value built gets.
    prov: Prov,
}

impl<'a> Builder<'a> {
    /// Starts a body for the values of one lifted region.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word's width, 32 or 64.
    /// * `temps` - The temporaries the lifter made, by id.
    /// * `vas` - The addresses of the instructions the values come from.
    pub(in super::super) fn new(word: u8, temps: &'a BTreeMap<u32, Expr>, vas: &[u64]) -> Self {
        let mut body = Body::new(word);
        let prov = body.prov(vas);
        Self { body, temps, prov }
    }

    /// Lowers a lifted value.
    ///
    /// # Arguments
    ///
    /// * `e` - The value.
    ///
    /// # Returns
    ///
    /// Its MIR value.
    pub(in super::super) fn value(&mut self, e: &Expr) -> Val {
        self.lower(e, EVAL_DEPTH)
    }

    /// Lowers a branch condition to a 1-bit value.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    ///
    /// # Returns
    ///
    /// Its MIR value, 1 when the condition holds.
    pub(in super::super) fn condition(&mut self, c: &Cond) -> Val {
        self.cond(c, EVAL_DEPTH)
    }

    /// Appends a value with the region's provenance.
    ///
    /// # Arguments
    ///
    /// * `inst` - Its operation.
    /// * `ty` - Its type.
    fn emit(&mut self, inst: Inst, ty: MTy) -> Val {
        self.body.push(inst, ty, self.prov)
    }

    /// Appends an input of the block's entry state, which no instruction
    /// computed.
    ///
    /// # Arguments
    ///
    /// * `inst` - The input: a register, the frame or the TLS block.
    /// * `ty` - Its type.
    fn input(&mut self, inst: Inst, ty: MTy) -> Val {
        self.body.push(inst, ty, Prov::ENTRY)
    }

    /// Appends an unknown value.
    ///
    /// # Arguments
    ///
    /// * `why` - Why it is unknown.
    fn undef(&mut self, why: Hole) -> Val {
        self.emit(Inst::Undef(why), MTy::I(64))
    }

    /// Appends an integer constant.
    ///
    /// # Arguments
    ///
    /// * `w` - Its width.
    /// * `bits` - Its bits, zero above `w`.
    fn konst(&mut self, w: u8, bits: u64) -> Val {
        self.emit(Inst::Const { w, bits }, MTy::I(w))
    }

    /// Returns an integer of `w` bits holding the bits of `v`: a float or
    /// address reinterpreted, then cut or zero-extended to the width.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    /// * `w` - The width, 1 to 64.
    fn int(&mut self, v: Val, w: u8) -> Val {
        let word = self.body.word;
        let ty = self.body.ty(v);
        let have = ty.bits(word);
        let v = match ty {
            MTy::I(_) => v,
            MTy::F32 | MTy::F64 | MTy::V(..) | MTy::Ptr => self.emit(
                Inst::Bitcast {
                    to: MTy::I(have),
                    x: v,
                },
                MTy::I(have),
            ),
        };
        match have.cmp(&w) {
            std::cmp::Ordering::Equal => v,
            std::cmp::Ordering::Greater => self.emit(Inst::Trunc { to: w, x: v }, MTy::I(w)),
            std::cmp::Ordering::Less => self.emit(
                Inst::Ext {
                    signed: false,
                    from: have,
                    to: w,
                    x: v,
                },
                MTy::I(w),
            ),
        }
    }

    /// Returns the low `fb` bits of `v` read as a float of that width.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    /// * `fb` - The width, 32 or 64; anything else reads as 64.
    fn reread(&mut self, v: Val, fb: u8) -> Val {
        let ty = if fb == 32 { MTy::F32 } else { MTy::F64 };
        if self.body.ty(v) == ty {
            return v;
        }
        let bits = self.int(v, ty.bits(64));
        self.emit(Inst::Bitcast { to: ty, x: bits }, ty)
    }

    /// Returns a float of type `ty`, converting a float of another width.
    ///
    /// # Arguments
    ///
    /// * `v` - The value, a float of `fb` bits.
    /// * `fb` - Its width.
    /// * `ty` - The type wanted.
    fn widen(&mut self, v: Val, fb: u8, ty: MTy) -> Val {
        let v = self.reread(v, fb);
        if self.body.ty(v) == ty {
            return v;
        }
        self.emit(
            Inst::Convert {
                to: ty,
                signed: false,
                x: v,
            },
            ty,
        )
    }

    /// Returns the float width of an expression, as the expression
    /// evaluator reads it, or `None` for an integer one.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    fn float_width(&self, e: &Expr) -> Option<u8> {
        self.float_width_in(e, EVAL_DEPTH)
    }

    /// [`Builder::float_width`] with a depth bound for temporaries.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `depth` - How much deeper to look.
    fn float_width_in(&self, e: &Expr, depth: u8) -> Option<u8> {
        let d = depth.checked_sub(1)?;
        match e {
            Expr::Deref(_, Ty::F32)
            | Expr::Cast(_, Ty::F32)
            | Expr::Bitcast(_, Ty::F32)
            | Expr::FConst(_, Ty::F32) => Some(32),
            Expr::Deref(_, Ty::F64)
            | Expr::Cast(_, Ty::F64)
            | Expr::Bitcast(_, Ty::F64)
            | Expr::FConst(_, Ty::F64) => Some(64),
            Expr::Var(Key::Tmp(id)) => self.float_width_in(self.temps.get(id)?, d),
            Expr::Bin(op, l, r) if op.is_float() => {
                Some(self.float_width_in(l, d)?.max(self.float_width_in(r, d)?))
            }
            Expr::Ternary(_, a, b) => super::super::expr::either_width(
                self.float_width_in(a, d),
                self.float_width_in(b, d),
            ),
            Expr::Un(_, inner) => self.float_width_in(inner, d),
            Expr::Helper(Helper::Rint, args) => {
                args.first().and_then(|a| self.float_width_in(a, d))
            }
            Expr::Const(_)
            | Expr::Var(_)
            | Expr::Str(_)
            | Expr::Sp(_)
            | Expr::Bin(..)
            | Expr::Deref(..)
            | Expr::Cond(_)
            | Expr::Sext(..)
            | Expr::Cast(..)
            | Expr::Bitcast(..)
            | Expr::Call(..)
            | Expr::Helper(..)
            | Expr::FConst(..) => None,
        }
    }

    /// Lowers an expression.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `depth` - How much deeper to lower; an expression deeper than the
    ///   evaluator reads is unknown.
    fn lower(&mut self, e: &Expr, depth: u8) -> Val {
        let Some(d) = depth.checked_sub(1) else {
            return self.undef(Hole::Depth);
        };
        let word = self.body.word;
        match e {
            Expr::Const(v) => {
                let w = if *v > super::super::verify::low(word) {
                    64
                } else {
                    word
                };
                self.konst(w, *v)
            }
            Expr::FConst(v, Ty::F32) => self.emit(
                Inst::FConst {
                    ty: MTy::F32,
                    bits: *v,
                },
                MTy::F32,
            ),
            Expr::FConst(v, Ty::F64) => self.emit(
                Inst::FConst {
                    ty: MTy::F64,
                    bits: *v,
                },
                MTy::F64,
            ),
            Expr::FConst(v, Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128) => self.konst(64, *v),
            Expr::Var(k @ (Key::Reg(_) | Key::A64(_))) => self.input(Inst::Reg(*k), MTy::I(64)),
            Expr::Var(Key::Tmp(id)) => match self.temps.get(id) {
                Some(t) => self.lower(t, d),
                None => self.undef(Hole::Var),
            },
            Expr::Var(Key::Slot(off)) => {
                let addr = self.input(Inst::Frame(*off), MTy::Ptr);
                self.emit(
                    Inst::Load {
                        addr,
                        ty: MTy::I(64),
                    },
                    MTy::I(64),
                )
            }
            Expr::Var(Key::Global(at, bits)) => {
                let addr = match tls_slot(*at) {
                    Some(off) => {
                        let tls = self.input(Inst::Tls, MTy::Ptr);
                        let tls = self.int(tls, word);
                        let off = self.konst(word, off & super::super::verify::low(word));
                        self.emit(
                            Inst::Bin {
                                op: BinOp::Add,
                                w: word,
                                l: tls,
                                r: off,
                            },
                            MTy::I(word),
                        )
                    }
                    None => self.konst(64, *at),
                };
                let ty = MTy::I(*bits);
                self.emit(Inst::Load { addr, ty }, ty)
            }
            Expr::Var(Key::Param(_)) => self.undef(Hole::Var),
            Expr::Str(_) => self.undef(Hole::Str),
            Expr::Sp(off) => self.input(Inst::Frame(*off), MTy::Ptr),
            Expr::Bin(op, l, r) if op.is_float() => {
                let (Some(fa), Some(fb)) = (self.float_width(l), self.float_width(r)) else {
                    return self.undef(Hole::Width);
                };
                let Some(ty) = MTy::of_float(fa.max(fb)) else {
                    return self.undef(Hole::Width);
                };
                let (a, b) = (self.lower(l, d), self.lower(r, d));
                let (a, b) = (self.widen(a, fa, ty), self.widen(b, fb, ty));
                self.fbin(*op, ty, a, b)
            }
            Expr::Bin(op, l, r) => {
                let (a, b) = (self.lower(l, d), self.lower(r, d));
                self.int_bin(*op, a, b)
            }
            Expr::Un(EUn::Neg, inner) if self.float_width(inner).is_some() => {
                let fb = self.float_width(inner).unwrap_or(64);
                let x = self.lower(inner, d);
                self.fun(FUnOp::Neg, x, fb)
            }
            Expr::Un(op @ (EUn::Sqrt | EUn::Fabs), inner) if self.float_width(inner).is_some() => {
                let fb = self.float_width(inner).unwrap_or(64);
                let x = self.lower(inner, d);
                let fop = if *op == EUn::Sqrt {
                    FUnOp::Sqrt
                } else {
                    FUnOp::Abs
                };
                self.fun(fop, x, fb)
            }
            Expr::Un(op @ (EUn::Neg | EUn::Not), inner) => {
                let x = self.lower(inner, d);
                let x = self.int(x, word);
                let op = if *op == EUn::Neg {
                    UnOp::Neg
                } else {
                    UnOp::Not
                };
                self.emit(Inst::Un { op, w: word, x }, MTy::I(word))
            }
            Expr::Un(..) => self.undef(Hole::Width),
            Expr::Deref(addr, ty) => {
                let a = self.lower(addr, d);
                let a = self.int(a, word);
                let ty = mty(*ty);
                self.emit(Inst::Load { addr: a, ty }, ty)
            }
            Expr::Cond(c) => self.cond(c, d),
            Expr::Ternary(c, a, b) => {
                let c = self.cond(c, d);
                let (fa, fb) = (self.float_width(a), self.float_width(b));
                let (t, f) = (self.lower(a, d), self.lower(b, d));
                let (t, f, ty) = match super::super::expr::either_width(fa, fb) {
                    Some(w) => {
                        let (t, f) = (self.reread(t, w), self.reread(f, w));
                        (t, f, if w == 32 { MTy::F32 } else { MTy::F64 })
                    }
                    None => {
                        let w = self
                            .body
                            .ty(t)
                            .bits(word)
                            .max(self.body.ty(f).bits(word))
                            .min(64);
                        (self.int(t, w), self.int(f, w), MTy::I(w))
                    }
                };
                self.emit(Inst::Select { c, t, f }, ty)
            }
            Expr::Sext(inner, bits) => {
                let x = self.lower(inner, d);
                self.sext(x, *bits)
            }
            Expr::Cast(inner, ty @ (Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64)) => {
                let x = self.lower(inner, d);
                let to = ty.bits();
                match self.float_width(inner) {
                    Some(fb) => {
                        let x = self.reread(x, fb);
                        self.emit(
                            Inst::Convert {
                                to: MTy::I(to),
                                signed: true,
                                x,
                            },
                            MTy::I(to),
                        )
                    }
                    None => self.int(x, to),
                }
            }
            Expr::Cast(_, Ty::U128) | Expr::Bitcast(_, Ty::U128) => self.undef(Hole::Width),
            Expr::Bitcast(inner, ty) => {
                let x = self.lower(inner, d);
                let bits = self.int(x, ty.bits());
                match mty(*ty) {
                    MTy::I(_) => bits,
                    to @ (MTy::F32 | MTy::F64 | MTy::V(..) | MTy::Ptr) => {
                        self.emit(Inst::Bitcast { to, x: bits }, to)
                    }
                }
            }
            Expr::Cast(inner, to @ (Ty::F32 | Ty::F64)) => self.float_cast(inner, *to, d),
            Expr::Helper(h, args) => self.helper(*h, args, d),
            Expr::Call(name, args) => {
                let lane = match name.as_str() {
                    "__dup_16b" => 8,
                    "__dup_8h" => 16,
                    "__dup_4s" => 32,
                    "__dup_2d" => 64,
                    _ => return self.undef(Hole::Op),
                };
                let Some(arg) = args.first() else {
                    return self.undef(Hole::Op);
                };
                let x = self.lower(arg, d);
                let x = self.int(x, 64);
                self.emit(Inst::Splat { lane, x }, MTy::V(64 / lane, Lane::I(lane)))
            }
        }
    }

    /// Sign-extends the low `bits` of a value to 64 bits; a width of 64 or
    /// more keeps the value whole, and zero is unknown.
    ///
    /// # Arguments
    ///
    /// * `x` - The value.
    /// * `bits` - The signed field's width.
    fn sext(&mut self, x: Val, bits: u8) -> Val {
        match bits {
            0 => self.undef(Hole::Width),
            64.. => self.int(x, 64),
            from => {
                let x = self.int(x, from);
                self.emit(
                    Inst::Ext {
                        signed: true,
                        from,
                        to: 64,
                        x,
                    },
                    MTy::I(64),
                )
            }
        }
    }

    /// Lowers a float cast of `inner` the way the expression evaluator
    /// reads it: a float converted, a float operation its own type does not
    /// say computed at the cast's width, a bitwise cut of a float's
    /// encoding reinterpreted, else an integer converted.
    ///
    /// # Arguments
    ///
    /// * `inner` - The cast's operand.
    /// * `to` - [`Ty::F32`] or [`Ty::F64`].
    /// * `d` - How much deeper to lower.
    fn float_cast(&mut self, inner: &Expr, to: Ty, d: u8) -> Val {
        let tb = to.bits();
        let ty = if tb == 32 { MTy::F32 } else { MTy::F64 };
        if let Some(fb) = self.float_width(inner) {
            let x = self.lower(inner, d);
            return if fb == tb {
                self.reread(x, fb)
            } else {
                self.widen(x, fb, ty)
            };
        }
        let wrong = |e: &Expr| matches!(e, Expr::FConst(_, t) if t.bits() != tb);
        match inner {
            Expr::Bin(op, _, _) if op.is_float() => return self.float_at(inner, tb, d),
            Expr::Un(op @ (EUn::Sqrt | EUn::Fabs), x) if !wrong(x) => {
                let x = self.lower(x, d);
                let fop = if *op == EUn::Sqrt {
                    FUnOp::Sqrt
                } else {
                    FUnOp::Abs
                };
                return self.fun(fop, x, tb);
            }
            Expr::Un(EUn::Neg, x) if x.is_float() && !wrong(x) => {
                let x = self.lower(x, d);
                return self.fun(FUnOp::Neg, x, tb);
            }
            Expr::Bin(op @ (Op::And | Op::Or | Op::Xor), l, r) if l.is_float() || r.is_float() => {
                let (a, b) = (self.lower(l, d), self.lower(r, d));
                let (a, b) = (self.int(a, 64), self.int(b, 64));
                let v = self.int_bin(*op, a, b);
                return self.reread(v, tb);
            }
            Expr::Const(_)
            | Expr::FConst(..)
            | Expr::Var(_)
            | Expr::Str(_)
            | Expr::Sp(_)
            | Expr::Bin(..)
            | Expr::Un(..)
            | Expr::Deref(..)
            | Expr::Cond(_)
            | Expr::Ternary(..)
            | Expr::Sext(..)
            | Expr::Cast(..)
            | Expr::Bitcast(..)
            | Expr::Call(..)
            | Expr::Helper(..) => {}
        }
        let (x, signed) = match inner {
            Expr::Sext(x, bits) => {
                let x = self.lower(x, d);
                (self.sext(x, *bits), true)
            }
            other => {
                let x = self.lower(other, d);
                (self.int(x, 64), false)
            }
        };
        self.emit(Inst::Convert { to: ty, signed, x }, ty)
    }

    /// Lowers a float operation whose operands carry no float type at the
    /// width `fb`, each operand's bits read as a float of that width.
    ///
    /// # Arguments
    ///
    /// * `e` - The operation; anything other than a float binary is
    ///   unknown, and so is one with a float constant of another width.
    /// * `fb` - The width, 32 or 64.
    /// * `d` - How much deeper to lower.
    fn float_at(&mut self, e: &Expr, fb: u8, d: u8) -> Val {
        let Expr::Bin(op, l, r) = e else {
            return self.undef(Hole::Width);
        };
        let wrong = |e: &Expr| matches!(e, Expr::FConst(_, t) if t.bits() != fb);
        let Some(ty) = MTy::of_float(fb).filter(|_| op.is_float() && !wrong(l) && !wrong(r)) else {
            return self.undef(Hole::Width);
        };
        let (a, b) = (self.lower(l, d), self.lower(r, d));
        let (a, b) = (self.reread(a, fb), self.reread(b, fb));
        self.fbin(*op, ty, a, b)
    }

    /// Appends a float binary operation.
    ///
    /// # Arguments
    ///
    /// * `op` - The expression's float operator.
    /// * `ty` - The type of both operands and the result.
    /// * `l` - The left operand.
    /// * `r` - The right operand.
    fn fbin(&mut self, op: Op, ty: MTy, l: Val, r: Val) -> Val {
        let op = match op {
            Op::FAdd => FOp::Add,
            Op::FSub => FOp::Sub,
            Op::FMul => FOp::Mul,
            Op::FDiv => FOp::Div,
            Op::FMin => FOp::MinX86,
            Op::FMax => FOp::MaxX86,
            Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Rem
            | Op::SDiv
            | Op::SRem
            | Op::And
            | Op::Or
            | Op::Xor
            | Op::Shl
            | Op::Shr
            | Op::Sar
            | Op::Rol(_)
            | Op::Ror(_)
            | Op::MulHi(_)
            | Op::SMulHi(_)
            | Op::SMulO(_)
            | Op::UAddO(_)
            | Op::USubO(_) => return self.undef(Hole::Op),
        };
        self.emit(Inst::FBin { op, ty, l, r }, ty)
    }

    /// Appends a float unary operation on the low `fb` bits of `x`.
    ///
    /// # Arguments
    ///
    /// * `op` - The operation.
    /// * `x` - The operand.
    /// * `fb` - The float's width, 32 or 64.
    fn fun(&mut self, op: FUnOp, x: Val, fb: u8) -> Val {
        let Some(ty) = MTy::of_float(fb) else {
            return self.undef(Hole::Width);
        };
        let x = self.reread(x, fb);
        self.emit(Inst::FUn { op, ty, x }, ty)
    }

    /// Appends an integer operator of the expression vocabulary: at the
    /// machine word, or at the width an operator names.
    ///
    /// # Arguments
    ///
    /// * `op` - The operator, not a float one.
    /// * `a` - The left operand.
    /// * `b` - The right operand.
    fn int_bin(&mut self, op: Op, a: Val, b: Val) -> Val {
        let word = self.body.word;
        let plain = |op| Some((op, word));
        let (inst, w) = match op {
            Op::Add => (plain(BinOp::Add), word),
            Op::Sub => (plain(BinOp::Sub), word),
            Op::Mul => (plain(BinOp::Mul), word),
            Op::Div => (plain(BinOp::UDiv), word),
            Op::Rem => (plain(BinOp::URem), word),
            Op::SDiv => (plain(BinOp::SDiv), word),
            Op::SRem => (plain(BinOp::SRem), word),
            Op::And => (plain(BinOp::And), word),
            Op::Or => (plain(BinOp::Or), word),
            Op::Xor => (plain(BinOp::Xor), word),
            Op::Shl => (plain(BinOp::Shl), word),
            Op::Shr => (plain(BinOp::LShr), word),
            Op::Sar => (plain(BinOp::AShr), word),
            Op::Rol(w) => (Some((BinOp::Rotl, w)), w),
            Op::Ror(w) => (Some((BinOp::Rotr, w)), w),
            Op::MulHi(w) => return self.wide(WideOp::UMulHi, w, a, b),
            Op::SMulHi(w) => return self.wide(WideOp::SMulHi, w, a, b),
            Op::SMulO(w) => return self.ovf(OvfOp::SMulO, w, a, b),
            Op::UAddO(w) => return self.ovf(OvfOp::UAddO, w, a, b),
            Op::USubO(w) => return self.ovf(OvfOp::USubO, w, a, b),
            Op::FAdd | Op::FSub | Op::FMul | Op::FDiv | Op::FMin | Op::FMax => (None, word),
        };
        let Some((op, w)) = inst.filter(|_| (1..=64).contains(&w)) else {
            return self.undef(Hole::Width);
        };
        let (l, r) = (self.int(a, w), self.int(b, w));
        let v = self.emit(Inst::Bin { op, w, l, r }, MTy::I(w));
        self.fit_word(v)
    }

    /// Appends the high half of a double-width product.
    ///
    /// # Arguments
    ///
    /// * `op` - Which product.
    /// * `w` - The operands' width.
    /// * `a` - The left operand.
    /// * `b` - The right operand.
    fn wide(&mut self, op: WideOp, w: u8, a: Val, b: Val) -> Val {
        if !(1..=64).contains(&w) {
            return self.undef(Hole::Width);
        }
        let (l, r) = (self.int(a, w), self.int(b, w));
        let v = self.emit(Inst::Wide { op, w, l, r }, MTy::I(w));
        self.fit_word(v)
    }

    /// Appends an overflow flag.
    ///
    /// # Arguments
    ///
    /// * `op` - Which operation's flag.
    /// * `w` - The operands' width.
    /// * `a` - The left operand.
    /// * `b` - The right operand.
    fn ovf(&mut self, op: OvfOp, w: u8, a: Val, b: Val) -> Val {
        if !(1..=64).contains(&w) {
            return self.undef(Hole::Width);
        }
        let (l, r) = (self.int(a, w), self.int(b, w));
        self.emit(Inst::Ovf { op, w, l, r }, MTy::I(1))
    }

    /// Cuts a value wider than the machine word to it, as every operator
    /// of an expression leaves its result.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    fn fit_word(&mut self, v: Val) -> Val {
        let word = self.body.word;
        if self.body.ty(v).bits(word) > word {
            self.int(v, word)
        } else {
            v
        }
    }

    /// Lowers a helper call.
    ///
    /// # Arguments
    ///
    /// * `h` - The helper.
    /// * `args` - Its arguments.
    /// * `d` - How much deeper to lower.
    fn helper(&mut self, h: Helper, args: &[Expr], d: u8) -> Val {
        let word = self.body.word;
        if let Helper::RoundToInt(_) = h {
            let Some(src) = args.first() else {
                return self.undef(Hole::Op);
            };
            let own = self.float_width(src);
            let Some(fb) = fcvt_float_width(args.get(1), own) else {
                return self.undef(Hole::Width);
            };
            let v = match src {
                Expr::Bin(op, ..) if op.is_float() && own.is_none() => self.float_at(src, fb, d),
                other => self.lower(other, d),
            };
            let v = self.int(v, 64);
            return self.emit(
                Inst::Helper {
                    h,
                    bits: fb,
                    word,
                    args: vec![v],
                },
                MTy::I(64),
            );
        }
        let first = args.first();
        let bits = match h.operands() {
            Operands::Float => match first.and_then(|a| self.float_width(a)) {
                Some(fb) => fb,
                None => return self.undef(Hole::Width),
            },
            Operands::Raw => first.map_or(word, |a| arg_bits(a, word)),
            Operands::Word { .. } | Operands::Wide => word,
        };
        let vals: Vec<Val> = args
            .iter()
            .map(|a| {
                let v = self.lower(a, d);
                self.int(v, 64)
            })
            .collect();
        let v = self.emit(
            Inst::Helper {
                h,
                bits,
                word,
                args: vals,
            },
            MTy::I(64),
        );
        if h == Helper::Rint && MTy::of_float(bits).is_some() {
            self.reread(v, bits)
        } else {
            v
        }
    }

    /// Lowers a condition to a 1-bit value, as the expression evaluator
    /// decides it: a float compare by its unordered rule, every other one
    /// at the width its flags were set at.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    /// * `d` - How much deeper to lower.
    fn cond(&mut self, c: &Cond, d: u8) -> Val {
        use ConditionCode as C;
        let cc = c.cc;
        match &c.flags {
            Flags::Float(..) | Flags::FCmp(..) => {
                return match c.fcmp() {
                    Some((pred, a, b, fb)) => self.fcmp(pred, a, b, fb, d),
                    None => self.undef(Hole::Flags),
                };
            }
            Flags::Cmp(a, b, _) => {
                if let Some(fb) = self.float_width(a).or_else(|| self.float_width(b)) {
                    return match FPred::of_flags(cc.0) {
                        Some(pred) => self.fcmp(pred, a, b, fb, d),
                        None => self.undef(Hole::Flags),
                    };
                }
            }
            Flags::Test(..)
            | Flags::Result(..)
            | Flags::Add(..)
            | Flags::Carry(_)
            | Flags::Shift(..)
            | Flags::Truth(..)
            | Flags::Unknown => {}
        }
        match &c.flags {
            Flags::Cmp(a, b, bits) => {
                let Some(w) = width(*bits) else {
                    return self.undef(Hole::Width);
                };
                let (a, b) = (self.lower(a, d), self.lower(b, d));
                let (a, b) = (self.int(a, w), self.int(b, w));
                match cc.0 {
                    C::None | C::o | C::no => self.undef(Hole::Flags),
                    C::s | C::ns | C::p | C::np => {
                        let diff = self.emit(
                            Inst::Bin {
                                op: BinOp::Sub,
                                w,
                                l: a,
                                r: b,
                            },
                            MTy::I(w),
                        );
                        self.zero_test(cc, diff, w)
                    }
                    C::e | C::ne | C::b | C::ae | C::be | C::a | C::l | C::ge | C::le | C::g => {
                        match relation(cc) {
                            Some(pred) => self.icmp(pred, w, a, b),
                            None => self.undef(Hole::Flags),
                        }
                    }
                }
            }
            Flags::Test(a, b, bits) => {
                let Some(w) = width(*bits) else {
                    return self.undef(Hole::Width);
                };
                let (a, b) = (self.lower(a, d), self.lower(b, d));
                let (l, r) = (self.int(a, w), self.int(b, w));
                let and = self.emit(
                    Inst::Bin {
                        op: BinOp::And,
                        w,
                        l,
                        r,
                    },
                    MTy::I(w),
                );
                self.zero_test(cc, and, w)
            }
            Flags::Result(e, bits) => {
                let Some(w) = width(*bits) else {
                    return self.undef(Hole::Width);
                };
                let x = self.lower(e, d);
                let x = self.int(x, w);
                self.zero_test(cc, x, w)
            }
            Flags::Shift(e, bits, count) => {
                let Some(w) = width(*bits) else {
                    return self.undef(Hole::Width);
                };
                let (x, c) = (self.lower(e, d), self.lower(count, d));
                let (x, c) = (self.int(x, w), self.int(c, 64));
                match cc.0 {
                    C::b => self.nonzero(c, 64, true),
                    C::ae => self.nonzero(c, 64, false),
                    C::be | C::a => {
                        let out = self.nonzero(c, 64, cc.0 == C::be);
                        let zero = self.nonzero(x, w, cc.0 == C::a);
                        let op = if cc.0 == C::be { BinOp::Or } else { BinOp::And };
                        self.emit(
                            Inst::Bin {
                                op,
                                w: 1,
                                l: out,
                                r: zero,
                            },
                            MTy::I(1),
                        )
                    }
                    C::o | C::no => self.undef(Hole::Flags),
                    C::None
                    | C::e
                    | C::ne
                    | C::s
                    | C::ns
                    | C::p
                    | C::np
                    | C::l
                    | C::ge
                    | C::le
                    | C::g => self.zero_test(cc, x, w),
                }
            }
            Flags::Carry(e) => {
                let x = self.lower(e, d);
                let x = self.int(x, 64);
                match cc.0 {
                    C::b | C::o => self.nonzero(x, 64, true),
                    C::ae | C::no => self.nonzero(x, 64, false),
                    C::None
                    | C::e
                    | C::ne
                    | C::be
                    | C::a
                    | C::s
                    | C::ns
                    | C::p
                    | C::np
                    | C::l
                    | C::ge
                    | C::le
                    | C::g => self.undef(Hole::Flags),
                }
            }
            Flags::Add(a, b, bits) => {
                let Some(w) = width(*bits) else {
                    return self.undef(Hole::Width);
                };
                let (a, b) = (self.lower(a, d), self.lower(b, d));
                let (l, r) = (self.int(a, w), self.int(b, w));
                self.add_flags(cc, l, r, w)
            }
            Flags::Truth(e, tcc) => {
                let x = self.lower(e, d);
                let x = self.int(x, 64);
                if cc == *tcc {
                    self.nonzero(x, 64, true)
                } else if cc == tcc.invert() {
                    self.nonzero(x, 64, false)
                } else {
                    self.undef(Hole::Flags)
                }
            }
            Flags::Float(..) | Flags::FCmp(..) | Flags::Unknown => self.undef(Hole::Flags),
        }
    }

    /// Lowers a float compare: both operands' low `fb` bits read as floats
    /// of that width, compared by the predicate.
    ///
    /// # Arguments
    ///
    /// * `pred` - The predicate.
    /// * `a` - The left operand.
    /// * `b` - The right operand.
    /// * `fb` - The width compared; anything other than 32 reads as 64.
    /// * `d` - How much deeper to lower.
    fn fcmp(&mut self, pred: FPred, a: &Expr, b: &Expr, fb: u8, d: u8) -> Val {
        let fb = if fb == 32 { 32 } else { 64 };
        let ty = if fb == 32 { MTy::F32 } else { MTy::F64 };
        let (l, r) = (self.lower(a, d), self.lower(b, d));
        let (l, r) = (self.reread(l, fb), self.reread(r, fb));
        self.emit(Inst::FCmp { pred, ty, l, r }, MTy::I(1))
    }

    /// Appends an integer compare.
    ///
    /// # Arguments
    ///
    /// * `pred` - The predicate.
    /// * `w` - The operands' width.
    /// * `l` - The left operand, `w` bits.
    /// * `r` - The right operand, `w` bits.
    fn icmp(&mut self, pred: IPred, w: u8, l: Val, r: Val) -> Val {
        self.emit(Inst::ICmp { pred, w, l, r }, MTy::I(1))
    }

    /// Appends the test of a `w`-bit value against zero.
    ///
    /// # Arguments
    ///
    /// * `x` - The value, `w` bits.
    /// * `w` - Its width.
    /// * `set` - Test for nonzero rather than zero.
    fn nonzero(&mut self, x: Val, w: u8, set: bool) -> Val {
        let zero = self.konst(w, 0);
        self.icmp(if set { IPred::Ne } else { IPred::Eq }, w, x, zero)
    }

    /// Appends a condition code read off flags a `w`-bit result set: the
    /// result compared with zero, or for `p` and `np` the parity of its
    /// low byte.
    ///
    /// # Arguments
    ///
    /// * `cc` - The condition code.
    /// * `x` - The result, `w` bits.
    /// * `w` - Its width.
    fn zero_test(&mut self, cc: Cc, x: Val, w: u8) -> Val {
        use ConditionCode as C;
        if matches!(cc.0, C::p | C::np) {
            let low = self.int(x, 8);
            let even = self.emit(
                Inst::Un {
                    op: UnOp::Parity,
                    w: 8,
                    x: low,
                },
                MTy::I(1),
            );
            return if cc.0 == C::p {
                even
            } else {
                let one = self.konst(1, 1);
                self.emit(
                    Inst::Bin {
                        op: BinOp::Xor,
                        w: 1,
                        l: even,
                        r: one,
                    },
                    MTy::I(1),
                )
            };
        }
        let pred = match cc.0 {
            C::s => Some(IPred::Slt),
            C::ns => Some(IPred::Sge),
            C::None
            | C::o
            | C::no
            | C::b
            | C::ae
            | C::e
            | C::ne
            | C::be
            | C::a
            | C::p
            | C::np
            | C::l
            | C::ge
            | C::le
            | C::g => relation(cc),
        };
        let Some(pred) = pred else {
            return self.undef(Hole::Flags);
        };
        let zero = self.konst(w, 0);
        self.icmp(pred, w, x, zero)
    }

    /// Appends a condition code read off the flags a `w`-bit addition
    /// sets.
    ///
    /// # Arguments
    ///
    /// * `cc` - The condition code.
    /// * `l` - The left addend, `w` bits.
    /// * `r` - The right addend, `w` bits.
    /// * `w` - The width.
    fn add_flags(&mut self, cc: Cc, l: Val, r: Val, w: u8) -> Val {
        use ConditionCode as C;
        let sum = self.emit(
            Inst::Bin {
                op: BinOp::Add,
                w,
                l,
                r,
            },
            MTy::I(w),
        );
        let bool_op = |b: &mut Self, op: BinOp, x: Val, y: Val| {
            b.emit(
                Inst::Bin {
                    op,
                    w: 1,
                    l: x,
                    r: y,
                },
                MTy::I(1),
            )
        };
        let not = |b: &mut Self, x: Val| {
            let one = b.konst(1, 1);
            b.emit(
                Inst::Bin {
                    op: BinOp::Xor,
                    w: 1,
                    l: x,
                    r: one,
                },
                MTy::I(1),
            )
        };
        match cc.0 {
            C::e | C::ne | C::s | C::ns | C::p | C::np => self.zero_test(cc, sum, w),
            C::l | C::ge | C::le | C::g => {
                let neg = self.zero_test(Cc(C::s), sum, w);
                let ovf = self.ovf(OvfOp::SAddO, w, l, r);
                let lt = bool_op(self, BinOp::Xor, neg, ovf);
                let le = if matches!(cc.0, C::le | C::g) {
                    let zero = self.zero_test(Cc(C::e), sum, w);
                    bool_op(self, BinOp::Or, lt, zero)
                } else {
                    lt
                };
                if matches!(cc.0, C::ge | C::g) {
                    not(self, le)
                } else {
                    le
                }
            }
            C::b | C::ae | C::o | C::no => {
                let op = if matches!(cc.0, C::b | C::ae) {
                    OvfOp::UAddO
                } else {
                    OvfOp::SAddO
                };
                let flag = self.ovf(op, w, l, r);
                if matches!(cc.0, C::ae | C::no) {
                    not(self, flag)
                } else {
                    flag
                }
            }
            C::None | C::be | C::a => self.undef(Hole::Flags),
        }
    }
}

/// The width a flags record compares at, cut to 64; `None` for zero.
///
/// # Arguments
///
/// * `bits` - The recorded width.
fn width(bits: u8) -> Option<u8> {
    (bits > 0).then_some(bits.min(64))
}

/// The integer predicate a condition code answers after a compare.
///
/// # Arguments
///
/// * `cc` - The condition code.
///
/// # Returns
///
/// The predicate, or `None` for a code that is no ordering of the two
/// operands (sign, overflow, parity).
fn relation(cc: Cc) -> Option<IPred> {
    use ConditionCode as C;
    Some(match cc.0 {
        C::e => IPred::Eq,
        C::ne => IPred::Ne,
        C::b => IPred::Ult,
        C::ae => IPred::Uge,
        C::be => IPred::Ule,
        C::a => IPred::Ugt,
        C::l => IPred::Slt,
        C::ge => IPred::Sge,
        C::le => IPred::Sle,
        C::g => IPred::Sgt,
        C::None | C::s | C::ns | C::o | C::no | C::p | C::np => return None,
    })
}

/// The machine type of an access type.
///
/// # Arguments
///
/// * `ty` - The access type.
fn mty(ty: Ty) -> MTy {
    match ty {
        Ty::U8 => MTy::I(8),
        Ty::U16 => MTy::I(16),
        Ty::U32 => MTy::I(32),
        Ty::U64 => MTy::I(64),
        Ty::U128 => MTy::I(128),
        Ty::F32 => MTy::F32,
        Ty::F64 => MTy::F64,
    }
}
