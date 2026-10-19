//! MIR: a typed, width-explicit SSA beside the lifter's [`super::expr::Expr`].
//!
//! A value is a [`Val`], an index into a [`Body`]'s arena, and has a
//! machine type ([`MTy`]): what its bits are, never what C calls them. An
//! integer has a width and no signedness; signedness lives on the ops
//! ([`BinOp::SDiv`], [`IPred::Slt`], [`Inst::Ext`]'s `signed`). Every
//! integer op holds the width it computes at, so a 32-bit difference is
//! [`Inst::Bin`] with `w: 32` over 32-bit operands and never a 64-bit one
//! plus a mask. A width change is an explicit [`Inst::Ext`] or
//! [`Inst::Trunc`], a reinterpretation of the same bits a [`Inst::Bitcast`],
//! and a value conversion a [`Inst::Convert`]; no op means two of these.
//!
//! The op set is closed: an operation either maps to these variants or adds
//! one, and every consumer matches it exhaustively. What the lowering
//! cannot express is an [`Inst::Undef`] naming why ([`Hole`]), which the
//! evaluator reads as unknown, never as a guess.
//!
//! Every value keeps a provenance id ([`Prov`]) that maps to the
//! instruction addresses it came from ([`Body::vas`]).
//!
//! Today MIR is built from the lifter's output ([`build`]), one body per
//! checked block, and run by its own evaluator ([`eval`]) with the
//! emulator's semantics, so [`super::verify`] can check the lifting
//! through MIR as it checks it through the expressions.

pub(super) mod build;
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "the e-graph is an opt-in pass; the tests and the measurement sweep are its callers"
    )
)]
pub(super) mod egraph;
pub(super) mod eval;
#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests;

use super::expr::Key;
use super::fcmp::FPred;
use super::helper::Helper;

/// An SSA value: the index of its defining node in [`Body::nodes`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Val(u32);

/// A provenance id: the index of a set of instruction addresses in
/// [`Body::provs`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct Prov(u32);

impl Prov {
    /// The id of a value no instruction computed: one the block's entry
    /// state holds.
    pub(super) const ENTRY: Self = Self(0);
}

/// The scalar type of one lane of a vector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Lane {
    /// An integer lane of this many bits, 8 to 64.
    I(u8),
}

/// A machine type: what a value's bits are.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum MTy {
    /// An integer of this many bits, 1 to 128, with no signedness.
    I(u8),
    /// An IEEE-754 single.
    F32,
    /// An IEEE-754 double.
    F64,
    /// A vector of this many lanes of one scalar type, at most 64 bits in
    /// all here.
    V(u8, Lane),
    /// An address at the machine word.
    Ptr,
}

impl MTy {
    /// Returns the type's width in bits.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word's width, which a [`MTy::Ptr`] has.
    pub(super) fn bits(self, word: u8) -> u8 {
        match self {
            Self::I(w) => w,
            Self::F32 => 32,
            Self::F64 => 64,
            Self::V(lanes, Lane::I(w)) => lanes.saturating_mul(w),
            Self::Ptr => word,
        }
    }

    /// Returns the float width of the type, or `None` for any other type.
    pub(super) fn float(self) -> Option<u8> {
        match self {
            Self::F32 => Some(32),
            Self::F64 => Some(64),
            Self::I(_) | Self::V(..) | Self::Ptr => None,
        }
    }

    /// Returns the float type of a width.
    ///
    /// # Arguments
    ///
    /// * `fb` - The width, 32 or 64.
    ///
    /// # Returns
    ///
    /// The type, or `None` for another width.
    pub(super) fn of_float(fb: u8) -> Option<Self> {
        match fb {
            32 => Some(Self::F32),
            64 => Some(Self::F64),
            _ => None,
        }
    }
}

/// An integer binary operation at an explicit width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum BinOp {
    /// Wrapping sum.
    Add,
    /// Wrapping difference.
    Sub,
    /// Wrapping product, the low half.
    Mul,
    /// Unsigned quotient; unknown for a zero divisor.
    UDiv,
    /// Signed quotient, wrapping; unknown for a zero divisor.
    SDiv,
    /// Unsigned remainder; unknown for a zero divisor.
    URem,
    /// Signed remainder, wrapping; unknown for a zero divisor.
    SRem,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise exclusive or.
    Xor,
    /// Shift left by the count modulo 64; a count of the width or more
    /// leaves zero.
    Shl,
    /// Logical shift right by the count modulo 64.
    LShr,
    /// Arithmetic shift right by the count modulo 64.
    AShr,
    /// Rotate left by the count modulo the width.
    Rotl,
    /// Rotate right by the count modulo the width.
    Rotr,
}

/// An overflow test: the 1-bit flag of an operation at a width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum OvfOp {
    /// The unsigned sum carries out.
    UAddO,
    /// The signed sum overflows.
    SAddO,
    /// The unsigned difference borrows.
    USubO,
    /// The signed product overflows.
    SMulO,
}

/// The high half of a double-width product.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum WideOp {
    /// Of the unsigned product.
    UMulHi,
    /// Of the signed product.
    SMulHi,
}

/// An integer unary operation at an explicit width.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum UnOp {
    /// Two's-complement negation.
    Neg,
    /// Bitwise not.
    Not,
    /// 1 when the low byte has an even number of set bits.
    Parity,
}

/// A float binary operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum FOp {
    /// Sum.
    Add,
    /// Difference.
    Sub,
    /// Product.
    Mul,
    /// Quotient.
    Div,
    /// `minss`: the left operand when the ordered `<` holds, else the right.
    MinX86,
    /// `maxss`: the left operand when the ordered `>` holds, else the right.
    MaxX86,
}

/// A float unary operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum FUnOp {
    /// The sign bit flipped.
    Neg,
    /// The sign bit cleared.
    Abs,
    /// The square root, rounded at the type's width.
    Sqrt,
}

/// An integer compare predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum IPred {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Unsigned less.
    Ult,
    /// Unsigned less or equal.
    Ule,
    /// Unsigned greater.
    Ugt,
    /// Unsigned greater or equal.
    Uge,
    /// Signed less.
    Slt,
    /// Signed less or equal.
    Sle,
    /// Signed greater.
    Sgt,
    /// Signed greater or equal.
    Sge,
}

/// Why the lowering left a value unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Hole {
    /// A variable the block's entry state does not hold (a parameter, a
    /// temporary no probe recorded).
    Var,
    /// A string literal, which has no bits here.
    Str,
    /// An operation of an unknown width or type: a float operation whose
    /// operands carry no float type, an operator whose width the
    /// expression does not record.
    Width,
    /// A named vector operation or a helper the lowering does not model.
    Op,
    /// Flags no instruction of the block set, or a condition they do not
    /// decide.
    Flags,
    /// An expression deeper than the evaluator reads.
    Depth,
}

/// One operation: a node of a [`Body`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) enum Inst {
    /// An integer constant of `w` bits.
    Const {
        /// The width.
        w: u8,
        /// The bits, zero above `w`.
        bits: u64,
    },
    /// A float constant.
    FConst {
        /// [`MTy::F32`] or [`MTy::F64`].
        ty: MTy,
        /// The encoding.
        bits: u64,
    },
    /// A register's value where the block starts, as the lifter keys it.
    Reg(Key),
    /// The stack pointer where the block starts, plus a byte offset.
    Frame(i64),
    /// The address of the thread's TLS block, as the entry state walks to
    /// it.
    Tls,
    /// The memory at an address as it was where the block started.
    Load {
        /// The address, at the machine word.
        addr: Val,
        /// The type read, which gives the bytes.
        ty: MTy,
    },
    /// An integer operation at width `w` of two `w`-bit operands.
    Bin {
        /// The operation.
        op: BinOp,
        /// The width.
        w: u8,
        /// The left operand.
        l: Val,
        /// The right operand.
        r: Val,
    },
    /// The 1-bit overflow flag of an operation at width `w`.
    Ovf {
        /// The operation.
        op: OvfOp,
        /// The width.
        w: u8,
        /// The left operand.
        l: Val,
        /// The right operand.
        r: Val,
    },
    /// The high `w` bits of a `2w`-bit product of two `w`-bit operands.
    Wide {
        /// The operation.
        op: WideOp,
        /// The width.
        w: u8,
        /// The left operand.
        l: Val,
        /// The right operand.
        r: Val,
    },
    /// An integer unary operation at width `w`.
    Un {
        /// The operation.
        op: UnOp,
        /// The width.
        w: u8,
        /// The operand.
        x: Val,
    },
    /// A `from`-bit integer extended to `to` bits.
    Ext {
        /// Sign-extend rather than zero-extend.
        signed: bool,
        /// The operand's width.
        from: u8,
        /// The result's width.
        to: u8,
        /// The operand.
        x: Val,
    },
    /// The low `to` bits of an integer.
    Trunc {
        /// The result's width.
        to: u8,
        /// The operand.
        x: Val,
    },
    /// The same bits as another type of the same width.
    Bitcast {
        /// The result's type.
        to: MTy,
        /// The operand.
        x: Val,
    },
    /// A value converted to another type: an integer to a float rounded
    /// to nearest, a float to a float rounded to nearest, or a float to an
    /// integer toward zero, the integer indefinite (the most negative
    /// value) when it does not fit, as `cvttsd2si` gives.
    Convert {
        /// The result's type.
        to: MTy,
        /// Whether an integer operand or result is signed.
        signed: bool,
        /// The operand.
        x: Val,
    },
    /// A float operation of two operands of type `ty`.
    FBin {
        /// The operation.
        op: FOp,
        /// [`MTy::F32`] or [`MTy::F64`].
        ty: MTy,
        /// The left operand.
        l: Val,
        /// The right operand.
        r: Val,
    },
    /// A float unary operation.
    FUn {
        /// The operation.
        op: FUnOp,
        /// [`MTy::F32`] or [`MTy::F64`].
        ty: MTy,
        /// The operand.
        x: Val,
    },
    /// A 1-bit integer compare of two `w`-bit operands.
    ICmp {
        /// The predicate.
        pred: IPred,
        /// The width.
        w: u8,
        /// The left operand.
        l: Val,
        /// The right operand.
        r: Val,
    },
    /// A 1-bit float compare of two operands of type `ty`.
    FCmp {
        /// The predicate.
        pred: FPred,
        /// [`MTy::F32`] or [`MTy::F64`].
        ty: MTy,
        /// The left operand.
        l: Val,
        /// The right operand.
        r: Val,
    },
    /// `t` when the 1-bit `c` is set, else `f`; only the chosen one is
    /// read.
    Select {
        /// The condition.
        c: Val,
        /// The value when set.
        t: Val,
        /// The value when clear.
        f: Val,
    },
    /// A `lane`-bit value repeated through 64 bits.
    Splat {
        /// The lane's width.
        lane: u8,
        /// The lane's value.
        x: Val,
    },
    /// A helper of the shared closed vocabulary ([`Helper`]), whose
    /// semantics [`Helper::eval`] holds.
    Helper {
        /// The helper.
        h: Helper,
        /// The width its operands are read at.
        bits: u8,
        /// The machine word's width.
        word: u8,
        /// The operands.
        args: Vec<Val>,
    },
    /// A value the lowering could not express.
    Undef(Hole),
}

/// One value of a [`Body`]: its operation, type and provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Node {
    /// The operation.
    pub(super) inst: Inst,
    /// The value's type.
    pub(super) ty: MTy,
    /// Where it came from.
    pub(super) prov: Prov,
}

/// The values of one lifted region, in definition order: each node reads
/// only nodes before it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Body {
    /// The machine word's width, 32 or 64: the width of an address.
    pub(super) word: u8,
    /// The values, indexed by [`Val`].
    pub(super) nodes: Vec<Node>,
    /// The instruction addresses each [`Prov`] stands for, indexed by it,
    /// in ascending order; none for [`Prov::ENTRY`].
    pub(super) provs: Vec<Vec<u64>>,
}

impl Body {
    /// Starts an empty body.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word's width, 32 or 64.
    pub(super) fn new(word: u8) -> Self {
        Self {
            word,
            nodes: Vec::new(),
            provs: vec![Vec::new()],
        }
    }

    /// Adds a provenance id for a set of instruction addresses.
    ///
    /// # Arguments
    ///
    /// * `vas` - The addresses, in any order.
    ///
    /// # Returns
    ///
    /// The id, the next in insertion order.
    pub(super) fn prov(&mut self, vas: &[u64]) -> Prov {
        let mut set = vas.to_vec();
        set.sort_unstable();
        set.dedup();
        let id = Prov(u32::try_from(self.provs.len()).unwrap_or(u32::MAX));
        self.provs.push(set);
        id
    }

    /// Returns the instruction addresses a provenance id stands for.
    ///
    /// # Arguments
    ///
    /// * `p` - The id.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "the divergence report reads provenance; the tests are its first caller"
        )
    )]
    pub(super) fn vas(&self, p: Prov) -> &[u64] {
        usize::try_from(p.0)
            .ok()
            .and_then(|i| self.provs.get(i))
            .map_or(&[], Vec::as_slice)
    }

    /// Appends a value.
    ///
    /// # Arguments
    ///
    /// * `inst` - Its operation.
    /// * `ty` - Its type.
    /// * `prov` - Where it came from.
    ///
    /// # Returns
    ///
    /// The value.
    pub(super) fn push(&mut self, inst: Inst, ty: MTy, prov: Prov) -> Val {
        let v = Val(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX));
        self.nodes.push(Node { inst, ty, prov });
        v
    }

    /// Returns a value's node.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    ///
    /// # Returns
    ///
    /// The node, or `None` for a value of another body.
    pub(super) fn node(&self, v: Val) -> Option<&Node> {
        usize::try_from(v.0).ok().and_then(|i| self.nodes.get(i))
    }

    /// Returns a value's type, [`MTy::I`] of 64 bits for a value of
    /// another body.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    pub(super) fn ty(&self, v: Val) -> MTy {
        self.node(v).map_or(MTy::I(64), |n| n.ty)
    }
}
