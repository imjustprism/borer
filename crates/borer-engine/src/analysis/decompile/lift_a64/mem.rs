//! Loads and stores for the arm64 lifter: one register or a pair, the
//! ordered forms, in every addressing mode.
//!
//! An address is the base plus an immediate or an extended, shifted index
//! register, or a literal's absolute address; off the stack pointer it is
//! a frame offset, so the access is a stack slot. A pre-indexed access
//! writes the address back to the base, a post-indexed one the base plus
//! the offset, after the access, the way the machine orders them. An
//! acquire or release form is its plain form, as for one thread it is.
//! A store-exclusive is that store and a status of zero, which is how the
//! machine runs it; it does not fail. An atomic is that load, the
//! modification, and the store, with the old value left in the destination;
//! `cas` stores only when memory matches, and either way leaves the old
//! value in the compare register.

use super::super::expr::{
    Cc, Cond, Expr, Flags, Key, Op, Ty, UnOp, either_width, fold, mask, mask_bits, sign_extend,
    ternary, unary,
};
use super::super::helper::Helper;
use super::super::lift::EffectKind;
use super::float::packed_name;
use super::simd::lane_of;
use super::{Lift, low, shifted};
use crate::isa::a64::{self, Insn, Layout, Mode, Opnd, Reg, Rmw, Structure, Width};
use crate::isa::x86::ConditionCode;
use crate::num::from_usize;

/// A base register and the value an access writes back to it.
type WriteBack = Option<(Reg, Expr)>;

/// Bytes a whole `v` register moves.
const GROUP_BYTES: u64 = 16;

/// The type one element of `width` moves for a register of `bits`, and
/// whether the load sign-extends it.
///
/// A `v` register at a single's or a double's width moves a float, as the
/// x86 lifter's `movss` and `movsd` do, so the access itself types it.
///
/// # Arguments
///
/// * `width` - What the access moves.
/// * `r` - The register moved, whose class tells a float.
/// * `bits` - The register's width: 32 or 64, or 8 to 128 for a `v`
///   register.
fn access(width: Width, r: Reg, bits: u16) -> (Ty, bool) {
    let float = match r {
        Reg::V(_) => matches!(bits, 32 | 64),
        Reg::X(_) | Reg::Sp | Reg::Zr => false,
    };
    match width {
        Width::Reg => (
            match (bits, float) {
                (32, true) => Ty::F32,
                (64, true) => Ty::F64,
                _ => Ty::from_bits(u8::try_from(bits).unwrap_or(u8::MAX)),
            },
            false,
        ),
        Width::Byte => (Ty::U8, false),
        Width::Half => (Ty::U16, false),
        Width::SByte => (Ty::U8, true),
        Width::SHalf => (Ty::U16, true),
        Width::SWord => (Ty::U32, true),
    }
}

/// Returns the value a store of `ty` writes.
///
/// A register's value is cut to a narrower store's width, so a slot
/// holding it reads back as the bytes the store wrote. A float already
/// no wider than the store is left whole: masking it is a bitwise
/// operation on the number and prints as `(float)a & 0xffffffff`. A
/// wider float keeps the cut, which is the low bits of its encoding.
/// [`put_at`] types that cut as an integer, so the mask is not an
/// operation on the number. A whole register stored is its own
/// variable, which a prologue's save is recognized by.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `ty` - The store's type.
fn stored(v: Expr, ty: Ty) -> Expr {
    cut_to(v, ty, None)
}

/// [`stored`] when the value's width is already known.
///
/// `known` is that width. A float already no wider than the cut is left
/// whole, including one whose expression is only a register name. `None`
/// reads the width from `v`.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `ty` - The width the cut keeps.
/// * `known` - The width `v` was computed at, when the expression no
///   longer says.
fn cut_to(v: Expr, ty: Ty, known: Option<u8>) -> Expr {
    let bits = ty.bits();
    let fits = match known {
        Some(width) => width <= bits,
        None => float_fits(&v, bits),
    };
    if bits < 64 && fits {
        return v;
    }
    match bits {
        bits @ 1..=63 => low(v, u16::from(bits)),
        _ => v,
    }
}

/// The type and value a store writes.
///
/// A float whose width is the store's stays a float. A float of another
/// width is the bits the store keeps, written as an unsigned integer: a
/// wider value keeps its low bits, and a narrower one keeps its encoding
/// in the low bits with zeros above it, which is what a scalar write left
/// in the register. Storing those bits as a float would round them. A
/// float written out early is only the register's name by the time a
/// store reads it, so `known` is that width. `None` reads it from `v`.
/// A sign bit flipped or cleared on a name is an integer, stored as
/// that integer: a float store would convert it. An integer constant
/// stored at a float width is that float: assigning the integer would
/// convert it, and the bits the instruction writes are the float's.
/// An integer that is not a float at all (a general register moved into
/// the lane) is stored as that integer. A float store would convert it.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `ty` - The width the instruction stores, as [`access`] types a `v`
///   register.
/// * `known` - The width `v` was computed at, when the expression no
///   longer says.
fn put_at(v: Expr, ty: Ty, known: Option<u8>) -> (Ty, Expr) {
    let bits = ty.bits();
    if lane_sign(&v) && matches!(ty, Ty::F32 | Ty::F64) {
        let integer = if bits <= 32 { Ty::U32 } else { Ty::U64 };
        return (integer, cut_to(v, integer, None));
    }
    if known.is_none() && matches!(ty, Ty::F32 | Ty::F64) && matches!(v, Expr::Const(_)) {
        let cut = cut_to(v, ty, None);
        if let Expr::Const(bits) = cut {
            let bits = if ty.bits() <= 32 {
                bits & 0xffff_ffff
            } else {
                bits
            };
            return (ty, Expr::FConst(bits, ty));
        }
        return (ty, cut);
    }
    let have = known.or_else(|| float_width(&v));
    if matches!(ty, Ty::F32 | Ty::F64) && have.is_none() {
        let integer = if bits <= 32 { Ty::U32 } else { Ty::U64 };
        return (integer, cut_to(v, integer, None));
    }
    if let Some(have) = have
        && matches!(ty, Ty::F32 | Ty::F64)
        && have != bits
    {
        let integer = if bits <= 32 { Ty::U32 } else { Ty::U64 };
        let cut = if have < bits {
            encoding(v, have)
        } else {
            cut_to(v, integer, known)
        };
        return (integer, cut);
    }
    (ty, cut_to(v, ty, known))
}

/// The sign bit of a scalar lane, 32 or 64.
///
/// `fneg` xors this bit. `fabs` clears it. One definition, so the store
/// that recognizes the operation cannot drift from the operation that
/// builds it.
///
/// # Arguments
///
/// * `bits` - The lane, 32 or 64.
pub(super) fn lane_sign_bit(bits: u16) -> Option<u64> {
    match bits {
        32 => Some(0x8000_0000),
        64 => Some(0x8000_0000_0000_0000),
        _ => None,
    }
}

/// Whether `v` flips or clears one lane's sign bit.
///
/// That is `fneg` or `fabs` of a value that is not itself a float: the
/// register's name. A 32-bit `fabs` is then cut to its low half, and the
/// two masks fold into `& 0x7fffffff`. The bits are an integer. A float
/// store would convert them.
///
/// # Arguments
///
/// * `v` - The value a store writes.
fn lane_sign(v: &Expr) -> bool {
    match v {
        Expr::Bin(op, l, r) if bin_sign(*op, l, r) => true,
        Expr::Bin(Op::And, inner, m) if low_mask(m) => lane_sign(inner),
        Expr::Bin(Op::And, m, inner) if low_mask(m) => lane_sign(inner),
        Expr::Const(_)
        | Expr::FConst(_, _)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(_, _, _)
        | Expr::Un(_, _)
        | Expr::Deref(_, _)
        | Expr::Cond(_)
        | Expr::Ternary(_, _, _)
        | Expr::Sext(_, _)
        | Expr::Cast(_, _)
        | Expr::Call(_, _)
        | Expr::Helper(_, _) => false,
    }
}

/// Whether `l` and `r` under `op` are a lane's sign bit.
///
/// The constant may sit on either side. A clear is every bit but the
/// sign, or, once a 32-bit value has been cut to its low half, just the
/// low 31 bits.
///
/// # Arguments
///
/// * `op` - The bitwise operator.
/// * `l` - Its left operand.
/// * `r` - Its right operand.
fn bin_sign(op: Op, l: &Expr, r: &Expr) -> bool {
    let hit = |e: &Expr, sign: bool| sign_const(e, sign);
    match op {
        Op::Xor => hit(l, true) || hit(r, true),
        Op::And => hit(l, false) || hit(r, false),
        _ => false,
    }
}

/// Whether `e` is the sign bit, or every bit but the sign bit.
///
/// # Arguments
///
/// * `e` - A bitwise operand.
/// * `sign` - `true` for the sign bit alone (`fneg`), `false` for the
///   rest (`fabs`).
fn sign_const(e: &Expr, sign: bool) -> bool {
    let Expr::Const(c) = e else {
        return false;
    };
    [32, 64].into_iter().any(|bits| {
        let Some(b) = lane_sign_bit(bits) else {
            return false;
        };
        if sign {
            *c == b
        } else {
            *c == !b || *c == b.wrapping_sub(1)
        }
    })
}

/// Whether `e` is a mask of some low bits.
///
/// # Arguments
///
/// * `e` - A bitwise operand.
fn low_mask(e: &Expr) -> bool {
    let Expr::Const(c) = e else {
        return false;
    };
    c.checked_add(1).is_some_and(u64::is_power_of_two)
}

/// The lane's bits as an integer.
///
/// A float moved into a general register, or into a narrower lane, is
/// those bits. A cast of the number would be a different value. At 64
/// bits a mask of every bit folds away, so the value is ored with itself:
/// that is the bits, and it is an integer.
///
/// # Arguments
///
/// * `v` - The float.
/// * `bits` - The lane, 1 to 64. Zero is no bits.
pub(super) fn as_integer_bits(v: Expr, bits: u16) -> Expr {
    if bits >= 64 {
        fold(Op::Or, v.clone(), v, 64)
    } else if bits == 0 {
        Expr::Const(0)
    } else {
        mask(v, (1u64 << u32::from(bits)) - 1)
    }
}

/// The float width `v` carries, including a variable declared as one.
///
/// [`float_width`] sees a float expression. A parameter or a register the
/// instruction already typed has no float node, so `ty_of` supplies the
/// width the declaration recorded. A select or a float operation takes a
/// width when either side has one. Anything else is an integer.
///
/// # Arguments
///
/// * `v` - The value a store writes.
/// * `ty_of` - The declared float width of a variable, if it has one.
fn named_width(v: &Expr, ty_of: &dyn Fn(Key) -> Option<u8>) -> Option<u8> {
    if let Some(width) = float_width(v) {
        return Some(width);
    }
    match v {
        Expr::Var(k) => ty_of(*k),
        Expr::Ternary(_, a, b) => either_width(named_width(a, ty_of), named_width(b, ty_of)),
        Expr::Bin(op, l, r) if op.is_float() => {
            either_width(named_width(l, ty_of), named_width(r, ty_of))
        }
        Expr::Un(UnOp::Sqrt | UnOp::Fabs | UnOp::Neg, inner) => named_width(inner, ty_of),
        Expr::Helper(Helper::Fabs, args) => args.first().and_then(|a| named_width(a, ty_of)),
        Expr::Const(_)
        | Expr::FConst(_, _)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(_, _, _)
        | Expr::Un(_, _)
        | Expr::Deref(_, _)
        | Expr::Cond(_)
        | Expr::Sext(_, _)
        | Expr::Cast(_, _)
        | Expr::Call(_, _)
        | Expr::Helper(_, _) => None,
    }
}

/// The width of a float declaration, or `None` for an integer one.
///
/// # Arguments
///
/// * `ty` - The recorded type.
pub(super) fn float_ty_bits(ty: Ty) -> Option<u8> {
    match ty {
        Ty::F32 => Some(32),
        Ty::F64 => Some(64),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => None,
    }
}

/// The width of a float expression, or `None` when `v` is not one.
///
/// A select carries a width when either arm does. Two bare registers
/// carry none.
///
/// # Arguments
///
/// * `v` - The value a store writes.
pub(super) fn float_width(v: &Expr) -> Option<u8> {
    match v {
        Expr::Deref(_, ty) | Expr::Cast(_, ty) | Expr::FConst(_, ty) => {
            matches!(ty, Ty::F32 | Ty::F64).then_some(ty.bits())
        }
        Expr::Bin(op, l, r) if op.is_float() => Some(float_width(l)?.max(float_width(r)?)),
        Expr::Un(UnOp::Sqrt | UnOp::Fabs | UnOp::Neg, inner) => float_width(inner),
        Expr::Ternary(_, a, b) => either_width(float_width(a), float_width(b)),
        Expr::Helper(Helper::Fabs, args) => args.first().and_then(float_width),
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Cond(_)
        | Expr::Sext(..)
        | Expr::Call(..)
        | Expr::Helper(..) => None,
    }
}

/// Whether `v` is a float whose representation already fits in `bits`.
///
/// # Arguments
///
/// * `v` - The value a store writes.
/// * `bits` - The store's width.
fn float_fits(v: &Expr, bits: u8) -> bool {
    float_width(v).is_some_and(|width| width <= bits)
}

/// Stamps `t` on a float operation that carries no width of its own.
///
/// A scalar `fadd` of two bare `v` registers is a float add, and nothing
/// in the expression says whether the instruction was a single or a
/// double. A store of another width would then mask a number, or leave
/// the store a float and round. A value that already carries a width is
/// left alone: wrapping it would convert the number, and a load already
/// typed at the operation's width must not grow a cast. A value that is
/// not a float is left alone too, so a select of two bare registers still
/// has the high bits cut off by the write.
///
/// # Arguments
///
/// * `v` - The operation.
/// * `t` - The width the instruction computed it at.
pub(super) fn bear_width(v: Expr, t: Ty) -> Expr {
    if v.is_float() && float_width(&v).is_none() {
        Expr::Cast(Box::new(v), t)
    } else {
        v
    }
}

/// The low `have` bits of a float, which are its encoding.
///
/// # Arguments
///
/// * `v` - The float.
/// * `have` - Its width, 32 or fewer.
fn encoding(v: Expr, have: u8) -> Expr {
    mask(v, mask_bits(have))
}

/// A float read at a different width, as that operation reads it.
///
/// A scalar write leaves zeros above its lane. A wider operation uses
/// that encoding; converting the number would be a different value. A
/// narrower operation uses the low bits of a wider encoding, which is
/// not a rounding conversion. The cast names the width the operation
/// reads and keeps those bits. The expression's own width wins. `known`
/// is the width a parameter was declared at, which a name does not carry,
/// and only when that width is wider than the read: the bits above an
/// incoming narrower value were not cleared here.
/// The same width, or a value that is not a float, is unchanged.
///
/// # Arguments
///
/// * `v` - The value the register holds.
/// * `bits` - The width the operation reads, 32 or 64.
/// * `known` - The declared width, when `v` does not say.
pub(super) fn as_encoding_at(v: Expr, bits: u16, known: Option<u8>) -> Expr {
    let Ok(want) = u8::try_from(bits) else {
        return v;
    };
    let Some(have) = float_width(&v).or(known.filter(|&width| width > want)) else {
        return v;
    };
    if have != want && matches!(want, 32 | 64) && matches!(have, 32 | 64) {
        let wide = if want == 32 { Ty::F32 } else { Ty::F64 };
        let kept = if have < want { have } else { want };
        Expr::Cast(Box::new(encoding(v, kept)), wide)
    } else {
        v
    }
}

/// A register operand of a load or store, general or `v`, with its width.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `k` - The operand's position.
fn register(i: &Insn, k: usize) -> Option<(Reg, u16)> {
    match i.operands.get(k).copied()? {
        Opnd::Reg { reg, bits } => Some((reg, bits)),
        Opnd::None
        | Opnd::Shifted { .. }
        | Opnd::Imm(_)
        | Opnd::PcRel(_)
        | Opnd::Mem(_)
        | Opnd::Cond(_)
        | Opnd::Other => None,
    }
}

impl Lift<'_, '_> {
    /// The address a memory operand names, and the write-back it makes.
    ///
    /// # Arguments
    ///
    /// * `o` - The operand.
    ///
    /// # Returns
    ///
    /// The address the access is at, and the base register with the value
    /// a pre- or post-indexed form leaves in it; `None` when the operand is
    /// no memory operand or literal address.
    fn address(&self, o: Opnd) -> Option<(Expr, WriteBack)> {
        let m = match o {
            Opnd::PcRel(at) => return Some((Expr::Const(at), None)),
            Opnd::Mem(m) => m,
            Opnd::None
            | Opnd::Reg { .. }
            | Opnd::Shifted { .. }
            | Opnd::Imm(_)
            | Opnd::Cond(_)
            | Opnd::Other => return None,
        };
        let base = self.read(m.base);
        let indexed = match m.index {
            Some((reg, bits)) => fold(
                Op::Add,
                base.clone(),
                shifted(self.reg_at(reg, bits), bits, m.extend, m.shift, 64),
                64,
            ),
            None => base.clone(),
        };
        let at = fold(Op::Add, indexed, Expr::Const(m.disp.cast_unsigned()), 64);
        Some(match m.mode {
            Mode::Offset => (at, None),
            Mode::PreIndex => (at.clone(), Some((m.base, at))),
            Mode::PostIndex => (base, Some((m.base, at))),
        })
    }

    /// The index a jump table's entry is loaded at: the index register,
    /// extended but not scaled, so case `k` is entry `k`; the base when it
    /// is the index register that holds the table's address.
    ///
    /// # Arguments
    ///
    /// * `o` - The load's memory operand.
    fn table_index(&self, o: Opnd) -> Option<Expr> {
        let Opnd::Mem(m) = o else {
            return None;
        };
        let (reg, bits) = m.index?;
        let index = self.reg_at(reg, bits);
        let base = self.read(m.base);
        Some(match (&index, &base) {
            (Expr::Const(_), b) if !matches!(b, Expr::Const(_)) => base,
            _ => shifted(index, bits, m.extend, 0, 64),
        })
    }

    /// A load of one register (`ldr`, `ldur`, `ldar`, `ldxr`, `ldraa`, the
    /// literal form, and the narrow and signed forms).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register, then address.
    /// * `width` - What it moves.
    pub(super) fn load(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (rt, bits) = register(i, 0)?;
        let (addr, back) = self.address(i.operands[1])?;
        if self.table_load == Some(i.va) {
            self.ex.switch_idx = self.table_index(i.operands[1]);
        }
        let (ty, signed) = access(width, rt, bits);
        let v = self.ex.read_at(addr, ty);
        let v = if signed { sign_extend(v, ty.bits()) } else { v };
        let mut writes = vec![(rt, bits, v)];
        writes.extend(back.map(|(r, a)| (r, 64, a)));
        self.write_all(writes);
        Some(())
    }

    /// The type and value a store of `r` writes.
    ///
    /// A float written out early is only the register's name. Its width is
    /// the written expression's, and only while the register still reads as
    /// that name: a later write leaves its own expression. The register's
    /// first note can be a narrower earlier use of the same name, and that
    /// does not replace the value's width.
    ///
    /// # Arguments
    ///
    /// * `r` - The register stored.
    /// * `bits` - The width the register is read at.
    /// * `ty` - The width the instruction stores.
    fn put_reg(&self, r: Reg, bits: u16, ty: Ty) -> (Ty, Expr) {
        let held = self.reg_at(r, bits);
        let ty_of = |k: Key| {
            self.ex
                .early_value(k)
                .and_then(float_width)
                .or_else(|| self.ex.ctx.reg_ty.get(&k).copied().and_then(float_ty_bits))
        };
        let known = named_width(&held, &ty_of);
        put_at(held, ty, known)
    }

    /// A store of one register (`str`, `stur`, `stlr`, and the narrow
    /// forms).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register, then address.
    /// * `width` - What it moves.
    pub(super) fn store(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (rt, bits) = register(i, 0)?;
        let (addr, back) = self.address(i.operands[1])?;
        let ty = access(width, rt, bits).0;
        self.note_stored_param(rt, ty);
        let (ty, v) = self.put_reg(rt, bits, ty);
        self.ex.store_at(addr, ty, v);
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
        Some(())
    }

    /// A store-exclusive of one register (`stxr`, `stlxr`), which always
    /// succeeds: the store, then status 0 at 32 bits, as the machine
    /// writes it. Ordering and a failed monitor add nothing it does.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: status, register, address.
    /// * `width` - What it moves.
    pub(super) fn store_exclusive(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (status, _) = register(i, 0)?;
        let (rt, bits) = register(i, 1)?;
        let (addr, _) = self.address(i.operands[2])?;
        let ty = access(width, rt, bits).0;
        self.note_stored_param(rt, ty);
        let (ty, v) = self.put_reg(rt, bits, ty);
        self.ex.store_at(addr, ty, v);
        self.write(status, 32, Expr::Const(0));
        Some(())
    }

    /// A store-exclusive of two registers (`stxp`, `stlxp`), which always
    /// succeeds: the two stores, then status 0 at 32 bits, as the machine
    /// writes it.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: status, two registers, address.
    pub(super) fn store_exclusive_pair(&mut self, i: &Insn) -> Option<()> {
        let (status, _) = register(i, 0)?;
        let (first, bits) = register(i, 1)?;
        let (second, _) = register(i, 2)?;
        let (ty, _) = access(Width::Reg, first, bits);
        self.note_stored_param(first, ty);
        self.note_stored_param(second, ty);
        let step = Expr::Const(from_usize(usize::from(bits / 8)));
        let (addr, _) = self.address(i.operands[3])?;
        let (ty_a, a) = self.put_reg(first, bits, ty);
        let (ty_b, b) = self.put_reg(second, bits, ty);
        self.ex.store_at(addr.clone(), ty_a, a);
        self.ex.store_at(fold(Op::Add, addr, step, 64), ty_b, b);
        self.write(status, 32, Expr::Const(0));
        Some(())
    }

    /// An atomic read-modify-write (`ldadd`, `ldclr`, `ldeor`, `ldset`,
    /// `ldsmax`, `ldsmin`, `ldumax`, `ldumin`, `swp`, in every ordering).
    ///
    /// Memory takes `op` of its old value and `Rs`, and `Rt` takes the old
    /// value. The old value is read into a temporary before anything is
    /// written, so `Rt` and `Rs` being one register still uses the value
    /// the instruction read, and a later read of `Rt` does not see the
    /// bytes the store just wrote. Ordering adds nothing one thread observes.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rs`, `Rt`, address.
    /// * `op` - The modification.
    /// * `width` - What it moves.
    pub(super) fn atomic(&mut self, i: &Insn, op: Rmw, width: Width) -> Option<()> {
        let (rs, bits) = register(i, 0)?;
        let (rt, _) = register(i, 1)?;
        let (addr, _) = self.address(i.operands[2])?;
        let ty = access(width, rt, bits).0;
        let n = ty.bits();
        let loaded = self.ex.read_at(addr.clone(), ty);
        let old = self.ex.tmp_of(&loaded, ty);
        let s = stored(self.reg_at(rs, bits), ty);
        let pick = |cc, kept: Expr, other: Expr| {
            ternary(
                Cond {
                    cc: Cc(cc),
                    flags: Flags::Cmp(kept.clone(), other.clone(), n),
                },
                kept,
                other,
            )
        };
        let new = match op {
            Rmw::Add => fold(Op::Add, old.clone(), s, n),
            Rmw::Clr => fold(Op::And, old.clone(), unary(UnOp::Not, s, n), n),
            Rmw::Eor => fold(Op::Xor, old.clone(), s, n),
            Rmw::Set => fold(Op::Or, old.clone(), s, n),
            Rmw::Smax => pick(ConditionCode::ge, old.clone(), s),
            Rmw::Smin => pick(ConditionCode::le, old.clone(), s),
            Rmw::Umax => pick(ConditionCode::ae, old.clone(), s),
            Rmw::Umin => pick(ConditionCode::be, old.clone(), s),
            Rmw::Swp => s,
        };
        self.write(rt, bits, old);
        self.ex.store_at(addr, ty, new);
        Some(())
    }

    /// `cas` in every ordering.
    ///
    /// Memory takes `Rt` when it equals `Rs`, and `Rs` takes the old value
    /// either way. The text is an `if` around that store; the recorded
    /// store is the old bytes when the compare fails, which is the memory
    /// the machine leaves. The old value is read before `Rs` is written, so
    /// the compare still sees the register the instruction read. Ordering
    /// adds nothing one thread observes.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: `Rs`, `Rt`, address.
    /// * `width` - What it moves.
    pub(super) fn compare_swap(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (rs, bits) = register(i, 0)?;
        let (rt, _) = register(i, 1)?;
        let (addr, _) = self.address(i.operands[2])?;
        let ty = access(width, rt, bits).0;
        let loaded = self.ex.read_at(addr.clone(), ty);
        let old = self.ex.tmp_of(&loaded, ty);
        let mut expect = stored(self.reg_at(rs, bits), ty);
        let mut new = stored(self.reg_at(rt, bits), ty);
        let mut at = addr;
        self.ex.settle_frame_region(&at, None, false, true);
        let mut seen = old.clone();
        self.ex.protect_memory_around(&mut [
            (&mut at, self.ex.word_ty()),
            (&mut new, ty),
            (&mut seen, ty),
            (&mut expect, ty),
        ]);
        let n = ty.bits();
        let new = match ty {
            Ty::U8 | Ty::U16 | Ty::U32 => crate::analysis::decompile::expr::low_bits_read(new, n),
            Ty::U64 | Ty::U128 | Ty::F32 | Ty::F64 => new,
        };
        let eq = Cond {
            cc: Cc(ConditionCode::e),
            flags: Flags::Cmp(seen.clone(), expect, n),
        };
        let kept = ternary(eq.clone(), new.clone(), seen);
        self.ex.note_escape(&kept);
        self.ex.note_escape(&at);
        if let Expr::Const(a) = at
            && self.ex.emit
            && self.ex.is_data(a)
        {
            self.ex.ctx.globals.insert((a, ty));
        }
        if let Some(p) = &mut self.ex.ctx.probe {
            p.store(&at, ty, &kept);
        }
        if self.ex.emit {
            let names = self.ex.names();
            let cond = eq.render(&names, false);
            let lhs = Expr::deref(at.clone(), ty).render(&names);
            let rhs = new.render(&names);
            self.ex.lines.push(format!("if ({cond}) {{"));
            self.ex.lines.push(format!("{lhs} = {rhs};"));
            self.ex.lines.push("}".to_owned());
        }
        self.ex.record(EffectKind::Store(Box::new((at, ty, kept))));
        self.write(rs, bits, old);
        Some(())
    }

    /// A load of two registers from consecutive elements (`ldp`, `ldnp`,
    /// `ldxp`, `ldaxp`, `ldpsw`).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: two registers, then address.
    /// * `width` - What each element moves.
    pub(super) fn load_pair(&mut self, i: &Insn, width: Width) -> Option<()> {
        let (first, bits) = register(i, 0)?;
        let (second, _) = register(i, 1)?;
        let (addr, back) = self.address(i.operands[2])?;
        let (ty, signed) = access(width, first, bits);
        let step = Expr::Const(u64::from(ty.bits() / 8));
        let a = self.ex.read_at(addr.clone(), ty);
        let b = self.ex.read_at(fold(Op::Add, addr, step, 64), ty);
        let extend = |v: Expr| if signed { sign_extend(v, ty.bits()) } else { v };
        let mut writes = vec![(first, bits, extend(a)), (second, bits, extend(b))];
        writes.extend(back.map(|(r, a)| (r, 64, a)));
        self.write_all(writes);
        Some(())
    }

    /// A store of two registers to consecutive elements (`stp`, `stnp`).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: two registers, then address.
    pub(super) fn store_pair(&mut self, i: &Insn) -> Option<()> {
        let (first, bits) = register(i, 0)?;
        let (second, _) = register(i, 1)?;
        let (ty, _) = access(Width::Reg, first, bits);
        self.note_stored_param(first, ty);
        self.note_stored_param(second, ty);
        let step = Expr::Const(from_usize(usize::from(bits / 8)));
        let (addr, _) = self.address(i.operands[2])?;
        let (ty_a, a) = self.put_reg(first, bits, ty);
        self.ex.store_at(addr, ty_a, a);
        let (addr, back) = self.address(i.operands[2])?;
        let (ty_b, b) = self.put_reg(second, bits, ty);
        self.ex.store_at(fold(Op::Add, addr, step, 64), ty_b, b);
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
        Some(())
    }

    /// `ld1` to `ld4` and `ld1r` to `ld4r` in every form
    /// ([`a64::structure`]), the base written back as its operand says.
    ///
    /// Whole registers are their blocks of memory, as a pair load's are.
    /// The interleaved forms read every block and name each register as
    /// the lanes it gathers from them, `__ld2_4s(b0, b1, 0)`; a lane form
    /// is that lane inserted (`__ins_4s`), a replicate form the element
    /// broadcast (`__dup_4s`), as the instructions with those names write
    /// them.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register list, then address.
    pub(super) fn load_structure(&mut self, i: &Insn) -> Option<()> {
        let s = a64::structure(i.word)?;
        let (addr, back) = self.address(i.operands[1])?;
        let (span, block) = block_of(&s);
        let elem = Ty::from_size(usize::from(s.elem / 8), false);
        let at = |k: u64| offset(&addr, k);
        let mut writes = Vec::with_capacity(usize::from(s.count) + 1);
        match s.layout {
            Layout::Blocks => {
                for k in 0..s.count {
                    let v = self.ex.read_at(at(u64::from(k) * span), block);
                    writes.push((s.reg(k), 128, v));
                }
            }
            Layout::Interleaved => {
                let blocks: Vec<Expr> = (0..s.count)
                    .map(|j| self.ex.read_at(at(u64::from(j) * span), block))
                    .collect();
                let name = packed_name(&format!("ld{}", s.count), s.elem, s.whole);
                for k in 0..s.count {
                    let mut args = blocks.clone();
                    args.push(Expr::Const(u64::from(k)));
                    writes.push((s.reg(k), 128, Expr::Call(name.clone(), args)));
                }
            }
            Layout::Lane(index) => {
                for k in 0..s.count {
                    let x = self.ex.read_at(at(u64::from(k) * elem_bytes(&s)), elem);
                    let args = vec![self.reg_at(s.reg(k), 128), x, Expr::Const(u64::from(index))];
                    writes.push((
                        s.reg(k),
                        128,
                        Expr::Call(packed_name("ins", s.elem, true), args),
                    ));
                }
            }
            Layout::Replicate => {
                for k in 0..s.count {
                    let x = self.ex.read_at(at(u64::from(k) * elem_bytes(&s)), elem);
                    let dup = Expr::Call(packed_name("dup", s.elem, s.whole), vec![x]);
                    writes.push((s.reg(k), 128, dup));
                }
            }
        }
        writes.extend(back.map(|(r, a)| (r, 64, a)));
        self.write_all(writes);
        Some(())
    }

    /// `st1` to `st4` in every form: the store counterpart of
    /// [`Lift::load_structure`]. An interleaved form stores each block as
    /// the lanes it gathers from the registers, `__st2_4s(v0, v1, 0)`; a
    /// lane form stores the lane.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction: register list, then address.
    pub(super) fn store_structure(&mut self, i: &Insn) -> Option<()> {
        let s = a64::structure(i.word)?;
        let (span, block) = block_of(&s);
        let regs: Vec<Expr> = (0..s.count).map(|k| self.reg_at(s.reg(k), 128)).collect();
        let name = packed_name(&format!("st{}", s.count), s.elem, s.whole);
        for (k, v) in (0u8..).zip(&regs) {
            let (addr, _) = self.address(i.operands[1])?;
            let (at, ty, v) = match s.layout {
                Layout::Blocks => (u64::from(k) * span, block, stored(v.clone(), block)),
                Layout::Interleaved => {
                    let mut args = regs.clone();
                    args.push(Expr::Const(u64::from(k)));
                    (u64::from(k) * span, block, Expr::Call(name.clone(), args))
                }
                Layout::Lane(index) => (
                    u64::from(k) * elem_bytes(&s),
                    Ty::from_size(usize::from(s.elem / 8), false),
                    lane_of(v.clone(), u32::from(index), s.elem),
                ),
                Layout::Replicate => return None,
            };
            self.ex.store_at(offset(&addr, at), ty, v);
        }
        let (_, back) = self.address(i.operands[1])?;
        if let Some((r, a)) = back {
            self.write(r, 64, a);
        }
        Some(())
    }
}

/// The bytes and type of one register's block of a structure access: a
/// whole register's sixteen, or the low half's eight.
///
/// # Arguments
///
/// * `s` - The structure.
fn block_of(s: &Structure) -> (u64, Ty) {
    if s.whole {
        (GROUP_BYTES, Ty::U128)
    } else {
        (GROUP_BYTES / 2, Ty::U64)
    }
}

/// The bytes one element of a structure access moves.
///
/// # Arguments
///
/// * `s` - The structure.
fn elem_bytes(s: &Structure) -> u64 {
    u64::from(s.elem / 8)
}

/// An address `k` bytes past another.
///
/// # Arguments
///
/// * `addr` - The address.
/// * `k` - The offset in bytes.
fn offset(addr: &Expr, k: u64) -> Expr {
    if k == 0 {
        addr.clone()
    } else {
        fold(Op::Add, addr.clone(), Expr::Const(k), 64)
    }
}
