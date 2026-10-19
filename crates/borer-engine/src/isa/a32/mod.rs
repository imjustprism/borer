//! ARM32: the A32 (ARM) and T32 (Thumb-2) instruction sets, decoded into
//! engine-owned instruction types.
//!
//! [`decode()`] turns the bytes at an address into an [`Insn`] whose
//! operation, operands, condition and control flow are engine types, in
//! either instruction set ([`Mode`]); [`text`] renders one as assembly and
//! [`Insn::registers`] says which registers it reads and writes. The
//! decoder is the engine's own: the integer data processing, multiplies
//! and divides, loads and stores in every addressing mode, the block
//! transfers, the branches, the bit operations, the `IT` blocks of T32,
//! and the scalar VFP instructions. An Advanced SIMD (NEON) word decodes
//! as [`Op::Neon`] and any other word the engine does not model as
//! [`Op::Unknown`]; both fall through. A word that decodes to no
//! instruction is [`Op::Invalid`].
//!
//! A T32 instruction inside an `IT` block takes its condition from the
//! block: the caller hands [`decode()`] the [`ItState`] the instructions
//! before it left, which the decode advances. A program says which
//! instruction set the code at an address is in through its [`Modes`].

mod arm;
mod fmt;
mod thumb;
mod vfp;

pub use super::a64::Cond;
pub use fmt::{name, text};

/// The stack pointer, `r13`.
pub const SP: Reg = Reg::R(13);
/// The link register, `r14`.
pub const LR: Reg = Reg::R(14);
/// The program counter, `r15`.
pub const PC: Reg = Reg::R(15);

/// The tag an address carries to name the test in front of an instruction
/// under a condition that moves control (`bxne lr`, `popeq {r4, pc}`,
/// `blne f`), rather than the instruction itself.
///
/// The test is no instruction of the code: the decompiler's blocks hold
/// it as the conditional branch around that instruction, at `va | SKIP`,
/// and a machine run from such an address tests the condition of the
/// instruction at `va`, going on to it when the condition holds and past
/// it when not. No ARM32 address reaches this bit.
pub const SKIP: u64 = 1 << 40;

/// Most instructions a run behind a [`SKIP`] test holds: the run of
/// instructions under one condition, ending in the one that moves control.
pub const RUN_MAX: usize = 16;

/// A register an operand names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Reg {
    /// A core register, `r0` to `r15`: `r13` is the stack pointer, `r14`
    /// the link register and `r15` the program counter.
    R(u8),
    /// A single-precision VFP register, `s0` to `s31`: the low (even) or
    /// high (odd) half of `d0` to `d15`.
    S(u8),
    /// A double-precision VFP register, `d0` to `d31`.
    D(u8),
}

/// The instruction set the code at an address is written in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mode {
    /// A32: four-byte instructions.
    Arm,
    /// T32: two- and four-byte instructions.
    Thumb,
}

/// Which instruction set each stretch of a program's code is in.
///
/// Sorted change points: the mode of an address is the one the last point
/// at or before it names, else [`Mode::Arm`]. A loader fills it from what
/// the file says (an ELF's mapping symbols and odd function addresses, a
/// Windows image's being Thumb throughout).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Modes(
    /// `(address, mode)` change points, sorted by address, one per address.
    pub Vec<(u64, Mode)>,
);

impl Modes {
    /// Returns the instruction set of the code at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    #[must_use]
    pub fn at(&self, va: u64) -> Mode {
        let k = self.0.partition_point(|p| p.0 <= va);
        k.checked_sub(1)
            .and_then(|k| self.0.get(k))
            .map_or(Mode::Arm, |p| p.1)
    }

    /// Builds the change points from marks in any order.
    ///
    /// Of two marks at one address the first given wins.
    ///
    /// # Arguments
    ///
    /// * `marks` - `(address, mode)` pairs.
    #[must_use]
    pub fn from_marks(mut marks: Vec<(u64, Mode)>) -> Modes {
        marks.sort_by_key(|m| m.0);
        marks.dedup_by_key(|m| m.0);
        Modes(marks)
    }
}

/// How a register operand is shifted before use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Shift {
    /// Logical shift left.
    Lsl,
    /// Logical shift right.
    Lsr,
    /// Arithmetic shift right.
    Asr,
    /// Rotate right.
    Ror,
    /// Rotate right by one through the carry flag.
    Rrx,
}

/// The second operand of a data-processing instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operand {
    /// An immediate, already rotated or expanded as the encoding states.
    Imm {
        /// The value.
        value: u32,
        /// The carry the expansion leaves, `None` when it leaves the carry
        /// flag as it is.
        carry: Option<bool>,
    },
    /// A register shifted by an immediate.
    Reg {
        /// The register.
        rm: Reg,
        /// The shift.
        shift: Shift,
        /// The shift amount, 0 to 32; 1 for [`Shift::Rrx`].
        amount: u8,
    },
    /// A register shifted by the low byte of another register.
    RegShift {
        /// The register shifted.
        rm: Reg,
        /// The shift; never [`Shift::Rrx`].
        shift: Shift,
        /// The register holding the amount.
        rs: Reg,
    },
}

/// A data-processing operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DpKind {
    /// `and`.
    And,
    /// `eor`.
    Eor,
    /// `sub`.
    Sub,
    /// `rsb`: the operand minus the register.
    Rsb,
    /// `add`.
    Add,
    /// `adc`: add with carry.
    Adc,
    /// `sbc`: subtract with carry as not-borrow.
    Sbc,
    /// `rsc`: reverse subtract with carry.
    Rsc,
    /// `tst`: the flags of `and`.
    Tst,
    /// `teq`: the flags of `eor`.
    Teq,
    /// `cmp`: the flags of `sub`.
    Cmp,
    /// `cmn`: the flags of `add`.
    Cmn,
    /// `orr`.
    Orr,
    /// `mov`, and the shifts (`lsl`, `lsr`, `asr`, `ror`, `rrx`).
    Mov,
    /// `bic`: and with the operand inverted.
    Bic,
    /// `mvn`: the operand inverted.
    Mvn,
    /// `orn` (T32): or with the operand inverted.
    Orn,
}

impl DpKind {
    /// Tells whether the operation only sets the flags: `tst`, `teq`,
    /// `cmp` and `cmn`.
    #[must_use]
    pub fn compares(self) -> bool {
        matches!(self, DpKind::Tst | DpKind::Teq | DpKind::Cmp | DpKind::Cmn)
    }

    /// Tells whether the operation reads no first register: `mov` and
    /// `mvn`.
    #[must_use]
    pub fn moves(self) -> bool {
        matches!(self, DpKind::Mov | DpKind::Mvn)
    }

    /// Tells whether the operation is arithmetic, whose flags carry an
    /// addition's or a subtraction's carry and overflow; a logical one
    /// takes its carry from the shifter and leaves the overflow alone.
    #[must_use]
    pub fn arithmetic(self) -> bool {
        matches!(
            self,
            DpKind::Sub
                | DpKind::Rsb
                | DpKind::Add
                | DpKind::Adc
                | DpKind::Sbc
                | DpKind::Rsc
                | DpKind::Cmp
                | DpKind::Cmn
        )
    }
}

/// How many bytes a load or store moves, and how a narrower load fills
/// the rest of its register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Width {
    /// Four bytes.
    Word,
    /// One byte, zero-extended.
    Byte,
    /// One byte, sign-extended.
    SByte,
    /// Two bytes, zero-extended.
    Half,
    /// Two bytes, sign-extended.
    SHalf,
}

impl Width {
    /// Returns the bytes the access moves.
    #[must_use]
    pub fn bytes(self) -> u8 {
        match self {
            Width::Word => 4,
            Width::Byte | Width::SByte => 1,
            Width::Half | Width::SHalf => 2,
        }
    }

    /// Tells whether a load sign-extends what it moves.
    #[must_use]
    pub fn signed(self) -> bool {
        matches!(self, Width::SByte | Width::SHalf)
    }
}

/// How a memory operand's address is formed and written back.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Index {
    /// `[rn, offset]`: the base is left as it is.
    Offset,
    /// `[rn, offset]!`: the access is at the base plus the offset, which is
    /// then written back to the base.
    Pre,
    /// `[rn], offset`: the access is at the base, which is then advanced
    /// by the offset.
    Post,
}

/// The offset of a memory operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Offset {
    /// A signed constant, in bytes.
    Imm(i32),
    /// A register, shifted, added or subtracted.
    Reg {
        /// The register.
        rm: Reg,
        /// Whether it is subtracted from the base.
        sub: bool,
        /// The shift.
        shift: Shift,
        /// The shift amount, 0 to 32.
        amount: u8,
    },
}

/// A memory operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Addr {
    /// The base register; [`PC`] for a literal, whose base is the program
    /// counter's value rounded down to a word.
    pub base: Reg,
    /// The offset.
    pub offset: Offset,
    /// How the address is formed and written back.
    pub index: Index,
}

/// The order a block transfer walks memory in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Block {
    /// Increment after: from the base up (`ldmia`, `pop`).
    Ia,
    /// Increment before: from the base plus four up.
    Ib,
    /// Decrement after: ending at the base.
    Da,
    /// Decrement before: ending below the base (`stmdb`, `push`).
    Db,
}

/// A VFP arithmetic operation of two sources.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FpOp {
    /// `vadd`.
    Add,
    /// `vsub`.
    Sub,
    /// `vmul`.
    Mul,
    /// `vdiv`.
    Div,
    /// `vnmul`: the product negated.
    Nmul,
    /// `vmla`: the destination plus the product, rounded twice.
    Mla,
    /// `vmls`: the destination minus the product, rounded twice.
    Mls,
    /// `vnmla`: the negated destination minus the product.
    Nmla,
    /// `vnmls`: the negated destination plus the product.
    Nmls,
    /// `vfma`: the destination plus the product, fused.
    Fma,
    /// `vfms`: the destination minus the product, fused.
    Fms,
    /// `vfnma`: the negated destination minus the product, fused.
    Fnma,
    /// `vfnms`: the negated destination plus the product, fused.
    Fnms,
}

/// A VFP operation of one source.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FpUn {
    /// `vmov` between registers of one precision.
    Mov,
    /// `vabs`.
    Abs,
    /// `vneg`.
    Neg,
    /// `vsqrt`.
    Sqrt,
}

/// A VFP conversion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Cvt {
    /// Single to double.
    SingleToDouble,
    /// Double to single.
    DoubleToSingle,
    /// A signed 32-bit integer to a float.
    SignedToFloat,
    /// An unsigned 32-bit integer to a float.
    UnsignedToFloat,
    /// A float to a signed 32-bit integer, rounding toward zero.
    FloatToSigned,
    /// A float to an unsigned 32-bit integer, rounding toward zero.
    FloatToUnsigned,
    /// A float to a signed 32-bit integer in the rounding mode `FPSCR`
    /// names (`vcvtr`).
    FloatToSignedR,
    /// A float to an unsigned 32-bit integer in the `FPSCR` rounding mode.
    FloatToUnsignedR,
}

/// What an instruction does, with its operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    /// A data-processing instruction: `rd = rn <kind> src`.
    Dp {
        /// The operation.
        kind: DpKind,
        /// The destination; unused by the compares.
        rd: Reg,
        /// The first source; unused by `mov` and `mvn`.
        rn: Reg,
        /// The second source.
        src: Operand,
    },
    /// `movw`: a 16-bit immediate, zero-extended.
    Movw {
        /// The destination.
        rd: Reg,
        /// The immediate.
        imm: u16,
    },
    /// `movt`: a 16-bit immediate into the top half, the bottom half kept.
    Movt {
        /// The destination.
        rd: Reg,
        /// The immediate.
        imm: u16,
    },
    /// `adr`, and an `add` or `sub` of an immediate to the program counter:
    /// an absolute address.
    Adr {
        /// The destination.
        rd: Reg,
        /// The address.
        target: u64,
    },
    /// `mul`, `mla` and `mls`: the low word of a product, plus or minus an
    /// accumulator.
    Mul {
        /// The destination.
        rd: Reg,
        /// The first factor.
        rn: Reg,
        /// The second factor.
        rm: Reg,
        /// The accumulator, for `mla` and `mls`.
        acc: Option<Reg>,
        /// Whether the product is subtracted from the accumulator (`mls`).
        sub: bool,
    },
    /// `umull`, `smull`, `umlal` and `smlal`: a 64-bit product, plus the
    /// 64 bits the destination pair holds for the accumulating forms.
    MulLong {
        /// Whether the factors are signed.
        signed: bool,
        /// Whether the pair accumulates.
        acc: bool,
        /// The low word's register.
        lo: Reg,
        /// The high word's register.
        hi: Reg,
        /// The first factor.
        rn: Reg,
        /// The second factor.
        rm: Reg,
    },
    /// `smmul` and `smmla`: the high word of a signed product, plus an
    /// accumulator.
    Smmul {
        /// The destination.
        rd: Reg,
        /// The first factor.
        rn: Reg,
        /// The second factor.
        rm: Reg,
        /// The accumulator, for `smmla`.
        acc: Option<Reg>,
    },
    /// `smulbb` and its kin, and `smlabb` and its kin: the product of two
    /// signed halfwords, plus an accumulator.
    Smulxy {
        /// The destination.
        rd: Reg,
        /// The first factor's register.
        rn: Reg,
        /// The second factor's register.
        rm: Reg,
        /// The first factor is the top halfword, else the bottom.
        n_top: bool,
        /// The second factor is the top halfword, else the bottom.
        m_top: bool,
        /// The accumulator, for `smlaxy`.
        acc: Option<Reg>,
    },
    /// `sdiv` and `udiv`; a division by zero gives zero.
    Div {
        /// Whether the division is signed.
        signed: bool,
        /// The destination.
        rd: Reg,
        /// The dividend.
        rn: Reg,
        /// The divisor.
        rm: Reg,
    },
    /// `clz`.
    Clz {
        /// The destination.
        rd: Reg,
        /// The source.
        rm: Reg,
    },
    /// `rbit`.
    Rbit {
        /// The destination.
        rd: Reg,
        /// The source.
        rm: Reg,
    },
    /// `rev`: the bytes of the word reversed.
    Rev {
        /// The destination.
        rd: Reg,
        /// The source.
        rm: Reg,
    },
    /// `rev16`: the bytes of each halfword swapped.
    Rev16 {
        /// The destination.
        rd: Reg,
        /// The source.
        rm: Reg,
    },
    /// `revsh`: the bytes of the low halfword swapped, sign-extended.
    Revsh {
        /// The destination.
        rd: Reg,
        /// The source.
        rm: Reg,
    },
    /// `ssat` and `usat`: a register, shifted, clamped to a signed or an
    /// unsigned range of `bits` bits.
    Sat {
        /// Whether the range is signed (`ssat`).
        signed: bool,
        /// The destination.
        rd: Reg,
        /// The source.
        rn: Reg,
        /// The width of the range: 1 to 32 signed, 0 to 31 unsigned.
        bits: u8,
        /// The shift applied first, [`Shift::Lsl`] or [`Shift::Asr`].
        shift: Shift,
        /// The shift amount, 0 to 32.
        amount: u8,
    },
    /// `ubfx` and `sbfx`: a bit field extracted to bit 0.
    Bfx {
        /// Whether the field is sign-extended.
        signed: bool,
        /// The destination.
        rd: Reg,
        /// The source.
        rn: Reg,
        /// The field's lowest bit.
        lsb: u8,
        /// The field's width in bits, 1 to 32.
        width: u8,
    },
    /// `bfi` and `bfc`: a field of the destination replaced by the low
    /// bits of a register, or cleared.
    Bfi {
        /// The destination, whose other bits stay.
        rd: Reg,
        /// The source, `None` for `bfc`.
        rn: Option<Reg>,
        /// The field's lowest bit.
        lsb: u8,
        /// The field's width in bits, 1 to 32.
        width: u8,
    },
    /// `uxtb`, `uxth`, `sxtb`, `sxth` and their adding forms (`uxtab`,
    /// ...): a rotated register's low byte or halfword, extended.
    Extend {
        /// Whether it is sign-extended.
        signed: bool,
        /// The bits kept: 8 or 16.
        bits: u8,
        /// The destination.
        rd: Reg,
        /// The source.
        rm: Reg,
        /// The rotation right before the extension: 0, 8, 16 or 24.
        rotate: u8,
        /// The register added, for the adding forms.
        add: Option<Reg>,
    },
    /// A load of one register (`ldr`, `ldrb`, `ldrsh`, `ldrex`, ...).
    Load {
        /// What it moves.
        width: Width,
        /// The register loaded.
        rt: Reg,
        /// The address.
        addr: Addr,
    },
    /// A store of one register (`str`, `strb`, `strh`).
    Store {
        /// What it moves: [`Width::Word`], [`Width::Byte`] or
        /// [`Width::Half`].
        width: Width,
        /// The register stored.
        rt: Reg,
        /// The address.
        addr: Addr,
    },
    /// `ldrex`: a load, the exclusive monitor not modeled.
    LoadEx {
        /// What it moves.
        width: Width,
        /// The destination.
        rt: Reg,
        /// The address.
        addr: Addr,
    },
    /// `strex`: a store that always succeeds, with status zero.
    StoreEx {
        /// What it moves.
        width: Width,
        /// The status register.
        rd: Reg,
        /// The register stored.
        rt: Reg,
        /// The address.
        addr: Addr,
    },
    /// `ldrd`: two words into two registers.
    LoadDual {
        /// The register the first word goes to.
        rt: Reg,
        /// The register the second goes to.
        rt2: Reg,
        /// The address.
        addr: Addr,
    },
    /// `strd`: two registers into two words.
    StoreDual {
        /// The register stored first.
        rt: Reg,
        /// The register stored second.
        rt2: Reg,
        /// The address.
        addr: Addr,
    },
    /// `ldm` and `pop`: a word into each listed register, lowest register
    /// at the lowest address.
    Ldm {
        /// The base.
        rn: Reg,
        /// The registers, bit `n` for `rn`.
        regs: u16,
        /// Whether the base is written back.
        wback: bool,
        /// The order.
        block: Block,
    },
    /// `stm` and `push`.
    Stm {
        /// The base.
        rn: Reg,
        /// The registers, bit `n` for `rn`.
        regs: u16,
        /// Whether the base is written back.
        wback: bool,
        /// The order.
        block: Block,
    },
    /// `b`: a direct jump, taken under the instruction's condition.
    B {
        /// The target.
        target: u64,
    },
    /// `bl`: a direct call in the same instruction set.
    Bl {
        /// The target.
        target: u64,
    },
    /// `blx` to an immediate: a direct call into the other instruction set.
    Blx {
        /// The target.
        target: u64,
    },
    /// `blx` to a register: an indirect call, the instruction set from the
    /// address's low bit.
    BlxReg {
        /// The register holding the target.
        rm: Reg,
    },
    /// `bx`: an indirect jump, the instruction set from the address's low
    /// bit; `bx lr` returns.
    Bx {
        /// The register holding the target.
        rm: Reg,
    },
    /// `cbz` and `cbnz`.
    Cbz {
        /// The register tested.
        rn: Reg,
        /// The target.
        target: u64,
        /// Taken when the register is not zero (`cbnz`).
        nonzero: bool,
    },
    /// `tbb` and `tbh`: a jump forward by twice the byte or halfword a
    /// table at `rn` holds at index `rm`.
    Tb {
        /// Halfword entries (`tbh`), else bytes.
        half: bool,
        /// The table's base.
        rn: Reg,
        /// The index.
        rm: Reg,
    },
    /// `it`: up to four instructions after it run under a condition.
    It {
        /// The first instruction's condition.
        first: Cond,
        /// The mask: which of the rest take the condition or its inverse,
        /// and how many there are.
        mask: u8,
    },
    /// `svc`: a supervisor call.
    Svc {
        /// The immediate.
        imm: u32,
    },
    /// `udf`, `bkpt` and the permanently undefined words compilers emit as
    /// traps: execution does not go on.
    Trap,
    /// `nop`, the hints, the barriers and the preloads: no effect on data.
    Nop,
    /// `mrs rd, apsr`: the flags into a register.
    Mrs {
        /// The destination.
        rd: Reg,
    },
    /// `msr apsr_nzcvq, rn`: the flags from a register.
    Msr {
        /// The source.
        rn: Reg,
    },
    /// `vldr`: one VFP register from memory.
    VLoad {
        /// The register: `s` or `d`.
        vd: Reg,
        /// The address.
        addr: Addr,
    },
    /// `vstr`: one VFP register to memory.
    VStore {
        /// The register: `s` or `d`.
        vd: Reg,
        /// The address.
        addr: Addr,
    },
    /// `vldm` and `vpop`: consecutive VFP registers from memory.
    VLdm {
        /// The base.
        rn: Reg,
        /// The first register: `s` or `d`.
        first: Reg,
        /// How many registers.
        count: u8,
        /// Whether the base is written back.
        wback: bool,
        /// Decrement before (`vpush`'s order), else increment after.
        db: bool,
    },
    /// `vstm` and `vpush`.
    VStm {
        /// The base.
        rn: Reg,
        /// The first register: `s` or `d`.
        first: Reg,
        /// How many registers.
        count: u8,
        /// Whether the base is written back.
        wback: bool,
        /// Decrement before, else increment after.
        db: bool,
    },
    /// A VFP operation of two sources (and the destination, for the
    /// multiply-accumulates).
    FpBin {
        /// The operation.
        op: FpOp,
        /// The destination.
        vd: Reg,
        /// The first source.
        vn: Reg,
        /// The second source.
        vm: Reg,
    },
    /// A VFP operation of one source.
    FpUn {
        /// The operation.
        op: FpUn,
        /// The destination.
        vd: Reg,
        /// The source.
        vm: Reg,
    },
    /// `vmov` of an immediate.
    FpImm {
        /// The destination.
        vd: Reg,
        /// The eight-bit encoded immediate the precision expands.
        imm8: u8,
    },
    /// `vcmp` and `vcmpe`: the floating-point flags.
    FpCmp {
        /// The first value.
        vd: Reg,
        /// The second, `None` for zero.
        vm: Option<Reg>,
    },
    /// `vcvt` between precisions or between a float and an integer.
    Vcvt {
        /// The conversion.
        cvt: Cvt,
        /// The destination.
        vd: Reg,
        /// The source.
        vm: Reg,
    },
    /// `vmov` between a core register and a single.
    VmovCore {
        /// Into the core register, else into the single.
        to_core: bool,
        /// The core register.
        rt: Reg,
        /// The single.
        sn: Reg,
    },
    /// `vmov` between two core registers and a double.
    VmovPair {
        /// Into the core registers, else into the double.
        to_core: bool,
        /// The core register holding the low word.
        rt: Reg,
        /// The core register holding the high word.
        rt2: Reg,
        /// The double.
        dm: Reg,
    },
    /// `vmrs`: `FPSCR` into a register, or its flags into the APSR's when
    /// the register is `r15`.
    Vmrs {
        /// The destination; [`PC`] names the flags.
        rt: Reg,
    },
    /// `vmsr`: a register into `FPSCR`.
    Vmsr {
        /// The source.
        rt: Reg,
    },
    /// An Advanced SIMD (NEON) instruction, which the engine does not
    /// model; falls through.
    Neon {
        /// The core register a move from a lane writes.
        core: Option<Reg>,
        /// The base register an element or structure load or store writes
        /// back.
        base: Option<Reg>,
        /// Whether it stores to memory.
        stores: bool,
    },
    /// Any other instruction the engine does not model; falls through.
    Unknown,
    /// A word that decodes to no instruction; execution does not go on.
    Invalid,
}

/// How an instruction moves control, ignoring its condition.
///
/// A conditional `b` and `cbz` are [`Flow::CondJump`], while any other
/// instruction under a condition ([`Insn::predicated`]) has the flow it
/// has when the condition holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Flow {
    /// Falls through.
    Next,
    /// A direct jump taken under a condition; falls through otherwise.
    CondJump,
    /// A jump, direct or through a register or memory.
    Jump,
    /// A call.
    Call,
    /// A return: `bx lr`, a `pop` or `ldm` from the stack into `pc`.
    Return,
    /// A trap or an undecodable word: execution does not go on.
    Invalid,
}

/// The `IT` state: which of the next instructions run under which
/// condition, as the processor's `ITSTATE` holds it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct ItState(
    /// `ITSTATE`: the base condition in bits 7 to 5, then the condition's
    /// low bit and the mask in bits 4 to 0; zero outside a block.
    pub u8,
);

impl ItState {
    /// Tells whether an instruction is inside an `IT` block.
    #[must_use]
    pub fn active(self) -> bool {
        self.0 & 0xf != 0
    }

    /// Returns the condition the next instruction runs under.
    ///
    /// # Returns
    ///
    /// The condition, or `None` outside a block.
    #[must_use]
    pub fn cond(self) -> Option<Cond> {
        self.active().then(|| Cond::from_code(self.0 >> 4))
    }

    /// Moves past one instruction of the block.
    pub fn advance(&mut self) {
        if self.0 & 0x7 == 0 {
            self.0 = 0;
        } else {
            self.0 = (self.0 & 0xe0) | ((self.0 << 1) & 0x1f);
        }
    }

    /// Starts a block.
    ///
    /// # Arguments
    ///
    /// * `first` - The `it` instruction's condition.
    /// * `mask` - Its mask, nonzero.
    pub fn start(&mut self, first: Cond, mask: u8) {
        self.0 = (cond_code(first) << 4) | (mask & 0xf);
    }
}

/// Returns the one-byte code of a register: `r0`..`r15` as their
/// numbers, `s0`..`s31` from 16 and `d0`..`d31` from 48.
///
/// # Arguments
///
/// * `r` - The register.
#[must_use]
pub fn code(r: Reg) -> u8 {
    match r {
        Reg::R(n) => n & 0xf,
        Reg::S(n) => 16 + (n & 0x1f),
        Reg::D(n) => 48 + (n & 0x1f),
    }
}

/// Returns the register a [`code`] names.
///
/// # Arguments
///
/// * `c` - The code.
///
/// # Returns
///
/// The register, or `None` for a code past `d31`.
#[must_use]
pub fn from_code(c: u8) -> Option<Reg> {
    match c {
        0..=15 => Some(Reg::R(c)),
        16..=47 => Some(Reg::S(c - 16)),
        48..=79 => Some(Reg::D(c - 48)),
        _ => None,
    }
}

/// Returns the four-bit code of a condition.
///
/// # Arguments
///
/// * `c` - The condition.
#[must_use]
pub fn cond_code(c: Cond) -> u8 {
    match c {
        Cond::Eq => 0x0,
        Cond::Ne => 0x1,
        Cond::Hs => 0x2,
        Cond::Lo => 0x3,
        Cond::Mi => 0x4,
        Cond::Pl => 0x5,
        Cond::Vs => 0x6,
        Cond::Vc => 0x7,
        Cond::Hi => 0x8,
        Cond::Ls => 0x9,
        Cond::Ge => 0xa,
        Cond::Lt => 0xb,
        Cond::Gt => 0xc,
        Cond::Le => 0xd,
        Cond::Al => 0xe,
        Cond::Nv => 0xf,
    }
}

/// Returns the condition that holds exactly when `c` does not.
///
/// # Arguments
///
/// * `c` - The condition; `al` and `nv` are their own inverses here.
#[must_use]
pub fn invert(c: Cond) -> Cond {
    match c {
        Cond::Al | Cond::Nv => c,
        other => Cond::from_code(cond_code(other) ^ 1),
    }
}

/// One decoded instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Insn {
    /// Where it sits.
    pub va: u64,
    /// Its length in bytes: 2 or 4.
    pub len: u8,
    /// The instruction set it is in.
    pub mode: Mode,
    /// The condition it runs under: its own field, or its `IT` block's;
    /// [`Cond::Al`] when it always runs.
    pub cond: Cond,
    /// Whether it sets the flags (the `s` forms, and a 16-bit T32 data
    /// instruction outside an `IT` block).
    pub sets: bool,
    /// What it does.
    pub op: Op,
    /// The encoding: the A32 word, or a T32 instruction's first halfword
    /// in the top half and its second in the bottom (a 16-bit one's in the
    /// bottom alone).
    pub word: u32,
}

/// The registers an instruction reads and writes.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Registers {
    /// The registers read.
    pub reads: Vec<Reg>,
    /// The registers written.
    pub writes: Vec<Reg>,
}

impl Insn {
    /// Returns the address after it.
    #[must_use]
    pub fn next(&self) -> u64 {
        self.va.wrapping_add(u64::from(self.len))
    }

    /// Returns the value an operand reads for the program counter: the
    /// instruction's address plus 8 in A32, plus 4 in T32.
    #[must_use]
    pub fn pc(&self) -> u64 {
        match self.mode {
            Mode::Arm => self.va.wrapping_add(8),
            Mode::Thumb => self.va.wrapping_add(4),
        }
    }

    /// Returns the address a literal load or store reads: the program
    /// counter's value rounded down to a word, plus the offset.
    ///
    /// # Returns
    ///
    /// The address, or `None` when the instruction has no literal operand.
    #[must_use]
    pub fn literal(&self) -> Option<u64> {
        let addr = match self.op {
            Op::Load { addr, .. }
            | Op::Store { addr, .. }
            | Op::LoadDual { addr, .. }
            | Op::VLoad { addr, .. }
            | Op::VStore { addr, .. } => addr,
            Op::Dp { .. }
            | Op::Movw { .. }
            | Op::Movt { .. }
            | Op::Adr { .. }
            | Op::Mul { .. }
            | Op::MulLong { .. }
            | Op::Div { .. }
            | Op::Clz { .. }
            | Op::Rbit { .. }
            | Op::Rev { .. }
            | Op::Rev16 { .. }
            | Op::Revsh { .. }
            | Op::Smmul { .. }
            | Op::Smulxy { .. }
            | Op::Bfx { .. }
            | Op::Sat { .. }
            | Op::Bfi { .. }
            | Op::Extend { .. }
            | Op::LoadEx { .. }
            | Op::StoreEx { .. }
            | Op::StoreDual { .. }
            | Op::Ldm { .. }
            | Op::Stm { .. }
            | Op::B { .. }
            | Op::Bl { .. }
            | Op::Blx { .. }
            | Op::BlxReg { .. }
            | Op::Bx { .. }
            | Op::Cbz { .. }
            | Op::Tb { .. }
            | Op::It { .. }
            | Op::Svc { .. }
            | Op::Trap
            | Op::Nop
            | Op::Mrs { .. }
            | Op::Msr { .. }
            | Op::VLdm { .. }
            | Op::VStm { .. }
            | Op::FpBin { .. }
            | Op::FpUn { .. }
            | Op::FpImm { .. }
            | Op::FpCmp { .. }
            | Op::Vcvt { .. }
            | Op::VmovCore { .. }
            | Op::VmovPair { .. }
            | Op::Vmrs { .. }
            | Op::Vmsr { .. }
            | Op::Neon { .. }
            | Op::Unknown
            | Op::Invalid => return None,
        };
        match (addr.base, addr.offset, addr.index) {
            (PC, Offset::Imm(d), Index::Offset) => {
                Some((self.pc() & !3).wrapping_add_signed(i64::from(d)) & 0xffff_ffff)
            }
            _ => None,
        }
    }

    /// Returns where a direct branch or call goes.
    ///
    /// # Returns
    ///
    /// The target of `b`, `bl`, `blx` to an immediate, `cbz` and `cbnz`;
    /// `None` for every other instruction.
    #[must_use]
    pub fn target(&self) -> Option<u64> {
        match self.op {
            Op::B { target } | Op::Bl { target } | Op::Blx { target } | Op::Cbz { target, .. } => {
                Some(target)
            }
            Op::Dp { .. }
            | Op::Movw { .. }
            | Op::Movt { .. }
            | Op::Adr { .. }
            | Op::Mul { .. }
            | Op::MulLong { .. }
            | Op::Div { .. }
            | Op::Clz { .. }
            | Op::Rbit { .. }
            | Op::Rev { .. }
            | Op::Rev16 { .. }
            | Op::Revsh { .. }
            | Op::Smmul { .. }
            | Op::Smulxy { .. }
            | Op::Bfx { .. }
            | Op::Sat { .. }
            | Op::Bfi { .. }
            | Op::Extend { .. }
            | Op::Load { .. }
            | Op::Store { .. }
            | Op::LoadEx { .. }
            | Op::StoreEx { .. }
            | Op::LoadDual { .. }
            | Op::StoreDual { .. }
            | Op::Ldm { .. }
            | Op::Stm { .. }
            | Op::BlxReg { .. }
            | Op::Bx { .. }
            | Op::Tb { .. }
            | Op::It { .. }
            | Op::Svc { .. }
            | Op::Trap
            | Op::Nop
            | Op::Mrs { .. }
            | Op::Msr { .. }
            | Op::VLoad { .. }
            | Op::VStore { .. }
            | Op::VLdm { .. }
            | Op::VStm { .. }
            | Op::FpBin { .. }
            | Op::FpUn { .. }
            | Op::FpImm { .. }
            | Op::FpCmp { .. }
            | Op::Vcvt { .. }
            | Op::VmovCore { .. }
            | Op::VmovPair { .. }
            | Op::Vmrs { .. }
            | Op::Vmsr { .. }
            | Op::Neon { .. }
            | Op::Unknown
            | Op::Invalid => None,
        }
    }

    /// Tells whether the instruction runs under a condition other than by
    /// being a conditional branch: an A32 instruction with a condition
    /// field other than `al`, or one inside an `IT` block.
    #[must_use]
    pub fn predicated(&self) -> bool {
        !matches!(self.cond, Cond::Al | Cond::Nv) && !matches!(self.op, Op::B { .. })
    }

    /// Tells whether the instruction writes the program counter.
    #[must_use]
    pub fn writes_pc(&self) -> bool {
        match self.op {
            Op::Dp { kind, rd, .. } => !kind.compares() && rd == PC,
            Op::Load { rt, .. } => rt == PC,
            Op::Ldm { regs, .. } => regs & 0x8000 != 0,
            Op::Movw { rd, .. }
            | Op::Movt { rd, .. }
            | Op::Adr { rd, .. }
            | Op::Mul { rd, .. }
            | Op::Smmul { rd, .. }
            | Op::Smulxy { rd, .. }
            | Op::Div { rd, .. }
            | Op::Clz { rd, .. }
            | Op::Rbit { rd, .. }
            | Op::Rev { rd, .. }
            | Op::Rev16 { rd, .. }
            | Op::Revsh { rd, .. }
            | Op::Bfx { rd, .. }
            | Op::Sat { rd, .. }
            | Op::Bfi { rd, .. }
            | Op::Extend { rd, .. } => rd == PC,
            Op::MulLong { lo, hi, .. } => lo == PC || hi == PC,
            Op::Store { .. }
            | Op::LoadEx { .. }
            | Op::StoreEx { .. }
            | Op::LoadDual { .. }
            | Op::StoreDual { .. }
            | Op::Stm { .. }
            | Op::B { .. }
            | Op::Bl { .. }
            | Op::Blx { .. }
            | Op::BlxReg { .. }
            | Op::Bx { .. }
            | Op::Cbz { .. }
            | Op::Tb { .. }
            | Op::It { .. }
            | Op::Svc { .. }
            | Op::Trap
            | Op::Nop
            | Op::Mrs { .. }
            | Op::Msr { .. }
            | Op::VLoad { .. }
            | Op::VStore { .. }
            | Op::VLdm { .. }
            | Op::VStm { .. }
            | Op::FpBin { .. }
            | Op::FpUn { .. }
            | Op::FpImm { .. }
            | Op::FpCmp { .. }
            | Op::Vcvt { .. }
            | Op::VmovCore { .. }
            | Op::VmovPair { .. }
            | Op::Vmrs { .. }
            | Op::Vmsr { .. }
            | Op::Neon { .. }
            | Op::Unknown
            | Op::Invalid => false,
        }
    }

    /// Returns how the instruction moves control ([`Flow`]).
    #[must_use]
    pub fn flow(&self) -> Flow {
        match self.op {
            Op::B { .. } if matches!(self.cond, Cond::Al | Cond::Nv) => Flow::Jump,
            Op::B { .. } | Op::Cbz { .. } => Flow::CondJump,
            Op::Bl { .. } | Op::Blx { .. } | Op::BlxReg { .. } => Flow::Call,
            Op::Bx { rm } if rm == LR => Flow::Return,
            Op::Bx { .. } | Op::Tb { .. } => Flow::Jump,
            Op::Trap | Op::Invalid => Flow::Invalid,
            Op::Dp {
                kind: DpKind::Mov,
                src:
                    Operand::Reg {
                        rm: LR,
                        shift: Shift::Lsl,
                        amount: 0,
                    },
                ..
            } if self.writes_pc() => Flow::Return,
            Op::Ldm { rn: SP, .. } if self.writes_pc() => Flow::Return,
            Op::Load {
                addr:
                    Addr {
                        base: SP,
                        index: Index::Post,
                        ..
                    },
                ..
            } if self.writes_pc() => Flow::Return,
            _ if self.writes_pc() => Flow::Jump,
            Op::Dp { .. }
            | Op::Movw { .. }
            | Op::Movt { .. }
            | Op::Adr { .. }
            | Op::Mul { .. }
            | Op::MulLong { .. }
            | Op::Div { .. }
            | Op::Clz { .. }
            | Op::Rbit { .. }
            | Op::Rev { .. }
            | Op::Rev16 { .. }
            | Op::Revsh { .. }
            | Op::Smmul { .. }
            | Op::Smulxy { .. }
            | Op::Bfx { .. }
            | Op::Sat { .. }
            | Op::Bfi { .. }
            | Op::Extend { .. }
            | Op::Load { .. }
            | Op::Store { .. }
            | Op::LoadEx { .. }
            | Op::StoreEx { .. }
            | Op::LoadDual { .. }
            | Op::StoreDual { .. }
            | Op::Ldm { .. }
            | Op::Stm { .. }
            | Op::It { .. }
            | Op::Svc { .. }
            | Op::Nop
            | Op::Mrs { .. }
            | Op::Msr { .. }
            | Op::VLoad { .. }
            | Op::VStore { .. }
            | Op::VLdm { .. }
            | Op::VStm { .. }
            | Op::FpBin { .. }
            | Op::FpUn { .. }
            | Op::FpImm { .. }
            | Op::FpCmp { .. }
            | Op::Vcvt { .. }
            | Op::VmovCore { .. }
            | Op::VmovPair { .. }
            | Op::Vmrs { .. }
            | Op::Vmsr { .. }
            | Op::Neon { .. }
            | Op::Unknown => Flow::Next,
        }
    }

    /// Returns the registers the instruction reads and writes.
    ///
    /// The program counter is never listed. A write of a single is listed
    /// as is, and so is a write of a double: which halves alias which is
    /// the reader's business. An instruction under a condition reads what
    /// it writes, since its destination keeps its value when the condition
    /// fails. Control flow adds nothing: a call's arguments and a return's
    /// result are the calling convention's.
    #[must_use]
    pub fn registers(&self) -> Registers {
        let mut r = Registers::default();
        let addr = |r: &mut Registers, a: Addr| {
            r.reads.push(a.base);
            if let Offset::Reg { rm, .. } = a.offset {
                r.reads.push(rm);
            }
            if a.index != Index::Offset {
                r.writes.push(a.base);
            }
        };
        let list = |regs: u16| (0u8..16).filter(move |n| regs & (1 << n) != 0).map(Reg::R);
        match self.op {
            Op::Dp { kind, rd, rn, src } => {
                if !kind.moves() {
                    r.reads.push(rn);
                }
                match src {
                    Operand::Imm { .. } => {}
                    Operand::Reg { rm, .. } => r.reads.push(rm),
                    Operand::RegShift { rm, rs, .. } => r.reads.extend([rm, rs]),
                }
                if !kind.compares() {
                    r.writes.push(rd);
                }
            }
            Op::Movw { rd, .. } | Op::Adr { rd, .. } => r.writes.push(rd),
            Op::Movt { rd, .. } => {
                r.reads.push(rd);
                r.writes.push(rd);
            }
            Op::Mul {
                rd, rn, rm, acc, ..
            }
            | Op::Smmul { rd, rn, rm, acc }
            | Op::Smulxy {
                rd, rn, rm, acc, ..
            } => {
                r.reads.extend([rn, rm]);
                r.reads.extend(acc);
                r.writes.push(rd);
            }
            Op::MulLong {
                acc,
                lo,
                hi,
                rn,
                rm,
                ..
            } => {
                r.reads.extend([rn, rm]);
                if acc {
                    r.reads.extend([lo, hi]);
                }
                r.writes.extend([lo, hi]);
            }
            Op::Div { rd, rn, rm, .. } => {
                r.reads.extend([rn, rm]);
                r.writes.push(rd);
            }
            Op::Clz { rd, rm }
            | Op::Rbit { rd, rm }
            | Op::Rev { rd, rm }
            | Op::Rev16 { rd, rm }
            | Op::Revsh { rd, rm } => {
                r.reads.push(rm);
                r.writes.push(rd);
            }
            Op::Bfx { rd, rn, .. } | Op::Sat { rd, rn, .. } => {
                r.reads.push(rn);
                r.writes.push(rd);
            }
            Op::Bfi { rd, rn, .. } => {
                r.reads.push(rd);
                r.reads.extend(rn);
                r.writes.push(rd);
            }
            Op::Extend { rd, rm, add, .. } => {
                r.reads.push(rm);
                r.reads.extend(add);
                r.writes.push(rd);
            }
            Op::Load { rt, addr: a, .. } | Op::LoadEx { rt, addr: a, .. } => {
                addr(&mut r, a);
                r.writes.push(rt);
            }
            Op::Store { rt, addr: a, .. } => {
                r.reads.push(rt);
                addr(&mut r, a);
            }
            Op::StoreEx {
                rd, rt, addr: a, ..
            } => {
                r.reads.push(rt);
                addr(&mut r, a);
                r.writes.push(rd);
            }
            Op::LoadDual { rt, rt2, addr: a } => {
                addr(&mut r, a);
                r.writes.extend([rt, rt2]);
            }
            Op::StoreDual { rt, rt2, addr: a } => {
                r.reads.extend([rt, rt2]);
                addr(&mut r, a);
            }
            Op::Ldm {
                rn, regs, wback, ..
            } => {
                r.reads.push(rn);
                r.writes.extend(list(regs));
                if wback {
                    r.writes.push(rn);
                }
            }
            Op::Stm {
                rn, regs, wback, ..
            } => {
                r.reads.push(rn);
                r.reads.extend(list(regs));
                if wback {
                    r.writes.push(rn);
                }
            }
            Op::BlxReg { rm } | Op::Bx { rm } => r.reads.push(rm),
            Op::Cbz { rn, .. } => r.reads.push(rn),
            Op::Tb { rn, rm, .. } => r.reads.extend([rn, rm]),
            Op::Mrs { rd } => r.writes.push(rd),
            Op::Msr { rn } => r.reads.push(rn),
            Op::VLoad { vd, addr: a } => {
                addr(&mut r, a);
                r.writes.push(vd);
            }
            Op::VStore { vd, addr: a } => {
                r.reads.push(vd);
                addr(&mut r, a);
            }
            Op::VLdm {
                rn,
                first,
                count,
                wback,
                ..
            } => {
                r.reads.push(rn);
                r.writes.extend(run(first, count));
                if wback {
                    r.writes.push(rn);
                }
            }
            Op::VStm {
                rn,
                first,
                count,
                wback,
                ..
            } => {
                r.reads.push(rn);
                r.reads.extend(run(first, count));
                if wback {
                    r.writes.push(rn);
                }
            }
            Op::FpBin { op, vd, vn, vm } => {
                r.reads.extend([vn, vm]);
                if !matches!(
                    op,
                    FpOp::Add | FpOp::Sub | FpOp::Mul | FpOp::Div | FpOp::Nmul
                ) {
                    r.reads.push(vd);
                }
                r.writes.push(vd);
            }
            Op::FpUn { vd, vm, .. } | Op::Vcvt { vd, vm, .. } => {
                r.reads.push(vm);
                r.writes.push(vd);
            }
            Op::FpImm { vd, .. } => r.writes.push(vd),
            Op::FpCmp { vd, vm } => {
                r.reads.push(vd);
                r.reads.extend(vm);
            }
            Op::VmovCore { to_core, rt, sn } => {
                if to_core {
                    r.reads.push(sn);
                    r.writes.push(rt);
                } else {
                    r.reads.push(rt);
                    r.writes.push(sn);
                }
            }
            Op::VmovPair {
                to_core,
                rt,
                rt2,
                dm,
            } => {
                if to_core {
                    r.reads.push(dm);
                    r.writes.extend([rt, rt2]);
                } else {
                    r.reads.extend([rt, rt2]);
                    r.writes.push(dm);
                }
            }
            Op::Vmrs { rt } => {
                if rt != PC {
                    r.writes.push(rt);
                }
            }
            Op::Vmsr { rt } => r.reads.push(rt),
            Op::B { .. }
            | Op::Bl { .. }
            | Op::Blx { .. }
            | Op::It { .. }
            | Op::Svc { .. }
            | Op::Trap
            | Op::Nop
            | Op::Unknown
            | Op::Invalid => {}
            Op::Neon { core, base, .. } => {
                r.reads.extend(base);
                r.writes.extend(core);
                r.writes.extend(base);
            }
        }
        if self.predicated() && self.flow() == Flow::Next {
            let kept: Vec<Reg> = r.writes.clone();
            r.reads.extend(kept);
        }
        r.reads.retain(|x| *x != PC);
        r.writes.retain(|x| *x != PC);
        r.reads.dedup();
        r
    }
}

/// The registers of a block transfer of VFP registers: `count` of them
/// from `first` up.
///
/// # Arguments
///
/// * `first` - The first register: `s` or `d`.
/// * `count` - How many.
pub fn run(first: Reg, count: u8) -> impl Iterator<Item = Reg> {
    (0..count).filter_map(move |k| match first {
        Reg::S(n) => n.checked_add(k).filter(|n| *n < 32).map(Reg::S),
        Reg::D(n) => n.checked_add(k).filter(|n| *n < 32).map(Reg::D),
        Reg::R(_) => None,
    })
}

/// Decodes the instruction at the start of `bytes`.
///
/// # Arguments
///
/// * `bytes` - The bytes at `va`, at least as many as the instruction.
/// * `va` - The instruction's address.
/// * `mode` - The instruction set.
/// * `it` - The `IT` state the instructions before it left; advanced past
///   this one, or started when this one is an `it`. Ignored in A32.
///
/// # Returns
///
/// The instruction, or `None` when `bytes` is too short for it or `va` is
/// not aligned to the instruction set (four bytes for A32, two for T32).
#[must_use]
pub fn decode(bytes: &[u8], va: u64, mode: Mode, it: &mut ItState) -> Option<Insn> {
    match mode {
        Mode::Arm => {
            if !va.is_multiple_of(4) {
                return None;
            }
            let word = u32::from_le_bytes(bytes.get(..4)?.try_into().ok()?);
            Some(arm::decode(word, va))
        }
        Mode::Thumb => {
            if !va.is_multiple_of(2) {
                return None;
            }
            let hw1 = u16::from_le_bytes(bytes.get(..2)?.try_into().ok()?);
            let wide = thumb::wide(hw1);
            let hw2 = if wide {
                u16::from_le_bytes(bytes.get(2..4)?.try_into().ok()?)
            } else {
                0
            };
            let cond = it.cond();
            let mut insn = thumb::decode(hw1, hw2, va, cond.is_some());
            if let Some(c) = cond {
                insn.cond = c;
            }
            it.advance();
            if let Op::It { first, mask } = insn.op {
                it.start(first, mask);
            }
            Some(insn)
        }
    }
}

/// Sign-extends the low `bits` of `v`.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width of the field, 1 to 32.
fn sext(v: u32, bits: u32) -> i64 {
    let shift = 32 - bits;
    i64::from((v << shift).cast_signed() >> shift)
}

/// A branch target: an address plus a signed offset, wrapped to 32 bits.
///
/// # Arguments
///
/// * `base` - The program counter's value.
/// * `off` - The offset.
fn rel(base: u64, off: i64) -> u64 {
    base.wrapping_add_signed(off) & 0xffff_ffff
}
