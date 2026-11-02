//! RISC-V: the RV32 and RV64 base integer sets with the M, A, F, D, C,
//! Zicsr and Zifencei extensions (RV32GC and RV64GC), decoded into
//! engine-owned instruction types.
//!
//! [`decode()`] turns the bytes at an address into an [`Insn`] whose
//! operation and operands are engine types; a compressed (C) instruction
//! decodes to the operation it expands to, two bytes long. [`text`]
//! renders one as assembly with the aliases GNU objdump prints (`li`,
//! `mv`, `ret`, `beqz`, `sext.w`). The decoder is the engine's own. A word
//! of an extension the engine does not model (vector, bit manipulation,
//! half or quad precision, the privileged instructions other than `ecall`,
//! `ebreak` and the trap returns) decodes as [`Op::Unknown`] or
//! [`Op::System`] and falls through; a word that decodes to no instruction is [`Op::Invalid`].

mod compressed;
mod fmt;
mod regs;

pub use fmt::{name, text};
pub use regs::{Registers, code, from_code};

/// The zero register, `x0`.
pub const ZERO: Reg = Reg::X(0);
/// The return address register, `x1` (`ra`).
pub const RA: Reg = Reg::X(1);
/// The stack pointer, `x2` (`sp`).
pub const SP: Reg = Reg::X(2);
/// The alternate link register, `x5` (`t0`), which millicode calls use.
pub const T0: Reg = Reg::X(5);

/// How wide the integer registers are.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Xlen {
    /// RV32: 32-bit registers and addresses.
    X32,
    /// RV64: 64-bit registers and addresses.
    X64,
}

impl Xlen {
    /// Returns the register width in bits: `32` or `64`.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            Xlen::X32 => 32,
            Xlen::X64 => 64,
        }
    }

    /// Returns `v` cut to an address of this width.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    #[must_use]
    pub fn addr(self, v: u64) -> u64 {
        match self {
            Xlen::X32 => v & 0xffff_ffff,
            Xlen::X64 => v,
        }
    }
}

/// A register an operand names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Reg {
    /// An integer register, `x0` to `x31`; `x0` reads zero.
    X(u8),
    /// A floating-point register, `f0` to `f31`.
    F(u8),
}

/// The width of a memory access, and for a load whether it sign-extends.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Width {
    /// A byte, sign-extended.
    B,
    /// A byte, zero-extended.
    Bu,
    /// A halfword, sign-extended.
    H,
    /// A halfword, zero-extended.
    Hu,
    /// A word, sign-extended.
    W,
    /// A word, zero-extended (RV64).
    Wu,
    /// A doubleword (RV64).
    D,
}

impl Width {
    /// Returns the access size in bytes.
    #[must_use]
    pub fn bytes(self) -> u8 {
        match self {
            Width::B | Width::Bu => 1,
            Width::H | Width::Hu => 2,
            Width::W | Width::Wu => 4,
            Width::D => 8,
        }
    }
}

/// An integer operation of the register and immediate forms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Alu {
    /// `add`.
    Add,
    /// `sub`.
    Sub,
    /// `sll`: shift left.
    Sll,
    /// `slt`: set if less than, signed.
    Slt,
    /// `sltu`: set if less than, unsigned.
    Sltu,
    /// `xor`.
    Xor,
    /// `srl`: shift right, logical.
    Srl,
    /// `sra`: shift right, arithmetic.
    Sra,
    /// `or`.
    Or,
    /// `and`.
    And,
    /// `mul`: the low half of the product.
    Mul,
    /// `mulh`: the high half, signed by signed.
    Mulh,
    /// `mulhsu`: the high half, signed by unsigned.
    Mulhsu,
    /// `mulhu`: the high half, unsigned by unsigned.
    Mulhu,
    /// `div`: signed quotient.
    Div,
    /// `divu`: unsigned quotient.
    Divu,
    /// `rem`: signed remainder.
    Rem,
    /// `remu`: unsigned remainder.
    Remu,
}

/// A conditional branch's comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BrCond {
    /// `beq`.
    Eq,
    /// `bne`.
    Ne,
    /// `blt`: signed less than.
    Lt,
    /// `bge`: signed greater or equal.
    Ge,
    /// `bltu`: unsigned less than.
    Ltu,
    /// `bgeu`: unsigned greater or equal.
    Geu,
}

/// A CSR instruction's operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CsrOp {
    /// `csrrw`: read, then write.
    Rw,
    /// `csrrs`: read, then set bits.
    Rs,
    /// `csrrc`: read, then clear bits.
    Rc,
}

/// What a CSR instruction writes or masks with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CsrSrc {
    /// A register.
    Reg(Reg),
    /// A five-bit immediate (the `i` forms).
    Imm(u8),
}

/// An atomic memory operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AmoOp {
    /// `amoswap`.
    Swap,
    /// `amoadd`.
    Add,
    /// `amoxor`.
    Xor,
    /// `amoand`.
    And,
    /// `amoor`.
    Or,
    /// `amomin`: signed.
    Min,
    /// `amomax`: signed.
    Max,
    /// `amominu`.
    Minu,
    /// `amomaxu`.
    Maxu,
}

/// A floating-point format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Fmt {
    /// Single precision (F).
    S,
    /// Double precision (D).
    D,
}

/// An integer format a float conversion reads or writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntFmt {
    /// A signed word.
    W,
    /// An unsigned word.
    Wu,
    /// A signed doubleword (RV64).
    L,
    /// An unsigned doubleword (RV64).
    Lu,
}

/// A two-operand floating-point operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FArith {
    /// `fadd`.
    Add,
    /// `fsub`.
    Sub,
    /// `fmul`.
    Mul,
    /// `fdiv`.
    Div,
    /// `fmin`.
    Min,
    /// `fmax`.
    Max,
    /// `fsgnj`: the first operand with the second's sign.
    Sgnj,
    /// `fsgnjn`: the first operand with the second's sign flipped.
    Sgnjn,
    /// `fsgnjx`: the first operand's sign xored with the second's.
    Sgnjx,
}

/// A fused multiply-add's form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Fused {
    /// `fmadd`: `a * b + c`.
    Madd,
    /// `fmsub`: `a * b - c`.
    Msub,
    /// `fnmsub`: `-(a * b) + c`.
    Nmsub,
    /// `fnmadd`: `-(a * b) - c`.
    Nmadd,
}

/// A floating-point comparison writing 0 or 1 to an integer register.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FCmp {
    /// `feq`.
    Eq,
    /// `flt`.
    Lt,
    /// `fle`.
    Le,
}

/// What an instruction does.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op {
    /// `lui`: `rd` takes `imm`, the 20-bit field shifted up 12 and
    /// sign-extended.
    Lui {
        /// The destination.
        rd: Reg,
        /// The value written.
        imm: i64,
    },
    /// `auipc`: `rd` takes the instruction's address plus the shifted
    /// immediate.
    Auipc {
        /// The destination.
        rd: Reg,
        /// The address written.
        target: u64,
    },
    /// `jal`: jumps to `target`, the next address in `rd`.
    Jal {
        /// The link register; `x0` for a plain jump.
        rd: Reg,
        /// Where it goes.
        target: u64,
    },
    /// `jalr`: jumps to `rs1 + off` with the low bit cleared, the next
    /// address in `rd`.
    Jalr {
        /// The link register; `x0` for a plain jump.
        rd: Reg,
        /// The base.
        rs1: Reg,
        /// The offset.
        off: i64,
    },
    /// A conditional branch to `target`.
    Branch {
        /// The comparison.
        cond: BrCond,
        /// The left operand.
        rs1: Reg,
        /// The right operand.
        rs2: Reg,
        /// Where it goes when the comparison holds.
        target: u64,
    },
    /// An integer load from `rs1 + off`.
    Load {
        /// The size and extension.
        width: Width,
        /// The destination.
        rd: Reg,
        /// The base.
        rs1: Reg,
        /// The offset.
        off: i64,
    },
    /// An integer store of `rs2` to `rs1 + off`.
    Store {
        /// The size.
        width: Width,
        /// The value stored.
        rs2: Reg,
        /// The base.
        rs1: Reg,
        /// The offset.
        off: i64,
    },
    /// An integer operation with an immediate (`addi`, `slli`, `addiw`).
    Imm {
        /// The operation.
        op: Alu,
        /// The destination.
        rd: Reg,
        /// The register operand.
        rs1: Reg,
        /// The immediate: sign-extended, or the shift amount.
        imm: i64,
        /// Whether it is an RV64 `w` form, on the low 32 bits with the
        /// result sign-extended.
        word: bool,
    },
    /// An integer operation on two registers (`add`, `mul`, `subw`).
    Reg3 {
        /// The operation.
        op: Alu,
        /// The destination.
        rd: Reg,
        /// The left operand.
        rs1: Reg,
        /// The right operand.
        rs2: Reg,
        /// Whether it is an RV64 `w` form.
        word: bool,
    },
    /// `fence`, ordering memory accesses.
    Fence {
        /// The predecessor set, `iorw` from bit 3 down.
        pred: u8,
        /// The successor set, `iorw` from bit 3 down.
        succ: u8,
        /// The fence mode: `8` is `fence.tso`.
        fm: u8,
    },
    /// `fence.i`, ordering instruction fetches.
    FenceI,
    /// `ecall`: a system call.
    Ecall,
    /// `ebreak`: a breakpoint trap.
    Ebreak,
    /// A CSR read and write.
    Csr {
        /// The operation.
        op: CsrOp,
        /// The register the old value goes to.
        rd: Reg,
        /// The value written or the mask.
        src: CsrSrc,
        /// The CSR number.
        csr: u16,
    },
    /// `lr`: a load-reserved from `(rs1)`.
    Lr {
        /// `W` or `D`.
        width: Width,
        /// The destination.
        rd: Reg,
        /// The address.
        rs1: Reg,
        /// The ordering bits: `aq` in bit 1, `rl` in bit 0.
        order: u8,
    },
    /// `sc`: a store-conditional of `rs2` to `(rs1)`, 0 in `rd` on success.
    Sc {
        /// `W` or `D`.
        width: Width,
        /// The status.
        rd: Reg,
        /// The address.
        rs1: Reg,
        /// The value.
        rs2: Reg,
        /// The ordering bits.
        order: u8,
    },
    /// An atomic read-modify-write of `(rs1)` with `rs2`, the old value
    /// in `rd`.
    Amo {
        /// The operation.
        op: AmoOp,
        /// `W` or `D`.
        width: Width,
        /// The old value.
        rd: Reg,
        /// The address.
        rs1: Reg,
        /// The operand.
        rs2: Reg,
        /// The ordering bits.
        order: u8,
    },
    /// A floating-point instruction.
    Float(FOp),
    /// A return from a trap handler (`mret`, `sret`, `uret`) to the
    /// address its exception program counter CSR holds.
    TrapRet,
    /// A privileged instruction that falls through (`wfi`, `sfence.vma`).
    System,
    /// A valid instruction of an extension the engine does not model.
    Unknown,
    /// A word that decodes to no instruction, or the all-zero halfword.
    Invalid,
}

/// A floating-point instruction (F and D).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FOp {
    /// A float load (`flw`, `fld`) from `rs1 + off`.
    Load {
        /// The format.
        fmt: Fmt,
        /// The destination.
        rd: Reg,
        /// The base.
        rs1: Reg,
        /// The offset.
        off: i64,
    },
    /// A float store (`fsw`, `fsd`) of `rs2` to `rs1 + off`.
    Store {
        /// The format.
        fmt: Fmt,
        /// The value stored.
        rs2: Reg,
        /// The base.
        rs1: Reg,
        /// The offset.
        off: i64,
    },
    /// A two-operand float operation.
    Arith {
        /// The operation.
        op: FArith,
        /// The format.
        fmt: Fmt,
        /// The destination.
        rd: Reg,
        /// The left operand.
        rs1: Reg,
        /// The right operand.
        rs2: Reg,
        /// The rounding mode field, 7 for dynamic.
        rm: u8,
    },
    /// `fsqrt`.
    Sqrt {
        /// The format.
        fmt: Fmt,
        /// The destination.
        rd: Reg,
        /// The operand.
        rs1: Reg,
        /// The rounding mode field.
        rm: u8,
    },
    /// A fused multiply-add.
    Fused {
        /// The form.
        op: Fused,
        /// The format.
        fmt: Fmt,
        /// The destination.
        rd: Reg,
        /// The first factor.
        rs1: Reg,
        /// The second factor.
        rs2: Reg,
        /// The addend.
        rs3: Reg,
        /// The rounding mode field.
        rm: u8,
    },
    /// A float comparison into an integer register.
    Cmp {
        /// The comparison.
        op: FCmp,
        /// The format.
        fmt: Fmt,
        /// The integer destination.
        rd: Reg,
        /// The left operand.
        rs1: Reg,
        /// The right operand.
        rs2: Reg,
    },
    /// `fclass`: the operand's class as a mask in an integer register.
    Class {
        /// The format.
        fmt: Fmt,
        /// The integer destination.
        rd: Reg,
        /// The operand.
        rs1: Reg,
    },
    /// A float to integer conversion (`fcvt.w.s`).
    ToInt {
        /// The float format read.
        fmt: Fmt,
        /// The integer format written.
        int: IntFmt,
        /// The integer destination.
        rd: Reg,
        /// The float operand.
        rs1: Reg,
        /// The rounding mode field.
        rm: u8,
    },
    /// An integer to float conversion (`fcvt.s.w`).
    FromInt {
        /// The float format written.
        fmt: Fmt,
        /// The integer format read.
        int: IntFmt,
        /// The float destination.
        rd: Reg,
        /// The integer operand.
        rs1: Reg,
        /// The rounding mode field.
        rm: u8,
    },
    /// A float format conversion (`fcvt.d.s`, `fcvt.s.d`).
    Convert {
        /// The format read.
        from: Fmt,
        /// The format written.
        to: Fmt,
        /// The destination.
        rd: Reg,
        /// The operand.
        rs1: Reg,
        /// The rounding mode field.
        rm: u8,
    },
    /// A bit move from a float register to an integer one (`fmv.x.w`).
    MvToInt {
        /// The float format.
        fmt: Fmt,
        /// The integer destination.
        rd: Reg,
        /// The float operand.
        rs1: Reg,
    },
    /// A bit move from an integer register to a float one (`fmv.w.x`).
    MvFromInt {
        /// The float format.
        fmt: Fmt,
        /// The float destination.
        rd: Reg,
        /// The integer operand.
        rs1: Reg,
    },
}

/// How an instruction moves control.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Flow {
    /// Falls through.
    Next,
    /// A conditional branch: to its target, or on.
    CondJump,
    /// A jump, direct (`j`) or through a register (`jr`).
    Jump,
    /// A call: a `jal` or `jalr` that links in `ra` or `t0`.
    Call,
    /// A return: `jalr x0, 0(ra)`, `jalr x0, 0(t0)` from a millicode
    /// call, or a return from a trap handler.
    Return,
    /// A trap or an undecodable word: execution does not go on.
    Invalid,
}

/// One decoded instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Insn {
    /// Where it sits.
    pub va: u64,
    /// Its length in bytes: 2 for a compressed instruction, else 4.
    pub len: u8,
    /// What it does; a compressed instruction's is what it expands to.
    pub op: Op,
    /// The encoding: the 32-bit word, or the 16-bit halfword in the low
    /// half.
    pub word: u32,
}

impl Insn {
    /// Returns the address after it.
    #[must_use]
    pub fn next(&self) -> u64 {
        self.va.wrapping_add(u64::from(self.len))
    }

    /// Returns where a direct jump, call or branch goes.
    ///
    /// # Returns
    ///
    /// The target of a `jal` or a conditional branch, `None` for anything
    /// else.
    #[must_use]
    pub fn target(&self) -> Option<u64> {
        match self.op {
            Op::Jal { target, .. } | Op::Branch { target, .. } => Some(target),
            Op::Lui { .. }
            | Op::Auipc { .. }
            | Op::Jalr { .. }
            | Op::Load { .. }
            | Op::Store { .. }
            | Op::Imm { .. }
            | Op::Reg3 { .. }
            | Op::Fence { .. }
            | Op::FenceI
            | Op::Ecall
            | Op::Ebreak
            | Op::Csr { .. }
            | Op::Lr { .. }
            | Op::Sc { .. }
            | Op::Amo { .. }
            | Op::Float(_)
            | Op::TrapRet
            | Op::System
            | Op::Unknown
            | Op::Invalid => None,
        }
    }

    /// Returns how it moves control.
    ///
    /// A `jal` or `jalr` that links in `ra` or `t0` is a call, as the ISA
    /// manual's return-address hints read it; `jalr x0, 0(ra)` and
    /// `jalr x0, 0(t0)` return; any other `jal` or `jalr` is a jump.
    /// `ebreak` traps.
    #[must_use]
    pub fn flow(&self) -> Flow {
        let links = |rd: Reg| rd == RA || rd == T0;
        match self.op {
            Op::Branch { .. } => Flow::CondJump,
            Op::Jal { rd, .. } if links(rd) => Flow::Call,
            Op::Jal { .. } => Flow::Jump,
            Op::Jalr { rd, .. } if links(rd) => Flow::Call,
            Op::Jalr {
                rd: ZERO,
                rs1: RA | T0,
                off: 0,
            } => Flow::Return,
            Op::TrapRet => Flow::Return,
            Op::Jalr { .. } => Flow::Jump,
            Op::Ebreak | Op::Invalid => Flow::Invalid,
            Op::Lui { .. }
            | Op::Auipc { .. }
            | Op::Load { .. }
            | Op::Store { .. }
            | Op::Imm { .. }
            | Op::Reg3 { .. }
            | Op::Fence { .. }
            | Op::FenceI
            | Op::Ecall
            | Op::Csr { .. }
            | Op::Lr { .. }
            | Op::Sc { .. }
            | Op::Amo { .. }
            | Op::Float(_)
            | Op::System
            | Op::Unknown => Flow::Next,
        }
    }
}

/// Returns bits `lo` to `lo + n - 1` of `w`.
///
/// # Arguments
///
/// * `w` - The encoding.
/// * `lo` - The lowest bit.
/// * `n` - How many bits, 1 to 31.
fn field(w: u32, lo: u32, n: u32) -> u32 {
    (w >> lo) & ((1 << n) - 1)
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

/// Returns the integer register a five-bit field at `lo` names.
///
/// # Arguments
///
/// * `w` - The encoding.
/// * `lo` - The field's lowest bit.
fn x(w: u32, lo: u32) -> Reg {
    Reg::X(crate::num::lo8(u64::from(field(w, lo, 5))))
}

/// Returns the float register a five-bit field at `lo` names.
///
/// # Arguments
///
/// * `w` - The encoding.
/// * `lo` - The field's lowest bit.
fn f(w: u32, lo: u32) -> Reg {
    Reg::F(crate::num::lo8(u64::from(field(w, lo, 5))))
}

/// Returns a small field as a byte.
///
/// # Arguments
///
/// * `w` - The encoding.
/// * `lo` - The field's lowest bit.
/// * `n` - How many bits, at most 8.
fn small(w: u32, lo: u32, n: u32) -> u8 {
    crate::num::lo8(u64::from(field(w, lo, n)))
}

/// Returns the address `off` bytes from `va`, cut to the register width.
///
/// # Arguments
///
/// * `xlen` - The register width.
/// * `va` - The instruction's address.
/// * `off` - The signed offset.
fn rel(xlen: Xlen, va: u64, off: i64) -> u64 {
    xlen.addr(va.wrapping_add_signed(off))
}

/// Decodes the instruction at the start of `bytes`.
///
/// # Arguments
///
/// * `bytes` - The bytes at `va`, at least as many as the instruction.
/// * `va` - The instruction's address.
/// * `xlen` - The register width, which picks between the RV32 and RV64
///   meanings of the compressed encodings and allows the RV64-only ones.
///
/// # Returns
///
/// The instruction, or `None` when `bytes` is too short for it or `va` is
/// odd. An encoding longer than 32 bits decodes as a two-byte
/// [`Op::Invalid`].
#[must_use]
pub fn decode(bytes: &[u8], va: u64, xlen: Xlen) -> Option<Insn> {
    if !va.is_multiple_of(2) {
        return None;
    }
    let lo = crate::num::u16_le(bytes, 0)?;
    if lo & 3 != 3 {
        let op = compressed::decode(lo, va, xlen);
        return Some(Insn {
            va,
            len: 2,
            op,
            word: u32::from(lo),
        });
    }
    if lo & 0x1c == 0x1c {
        return Some(Insn {
            va,
            len: 2,
            op: Op::Invalid,
            word: u32::from(lo),
        });
    }
    let word = crate::num::u32_le(bytes, 0)?;
    Some(Insn {
        va,
        len: 4,
        op: decode32(word, va, xlen),
        word,
    })
}

/// Decodes a 32-bit instruction.
///
/// # Arguments
///
/// * `w` - The word.
/// * `va` - Its address.
/// * `xlen` - The register width.
fn decode32(w: u32, va: u64, xlen: Xlen) -> Op {
    let rd = x(w, 7);
    let rs1 = x(w, 15);
    let rs2 = x(w, 20);
    let f3 = field(w, 12, 3);
    let i_imm = sext(w >> 20, 12);
    let s_imm = sext((field(w, 25, 7) << 5) | field(w, 7, 5), 12);
    let rv64 = xlen == Xlen::X64;
    match field(w, 0, 7) {
        0x03 => match load_width(f3, rv64) {
            Some(width) => Op::Load {
                width,
                rd,
                rs1,
                off: i_imm,
            },
            None => Op::Invalid,
        },
        0x07 => match f3 {
            2 | 3 => Op::Float(FOp::Load {
                fmt: if f3 == 2 { Fmt::S } else { Fmt::D },
                rd: f(w, 7),
                rs1,
                off: i_imm,
            }),
            _ => Op::Unknown,
        },
        0x0f => match f3 {
            0 => Op::Fence {
                pred: small(w, 24, 4),
                succ: small(w, 20, 4),
                fm: small(w, 28, 4),
            },
            1 => Op::FenceI,
            _ => Op::Invalid,
        },
        0x13 => op_imm(w, rd, rs1, i_imm, rv64, false),
        0x1b if rv64 => op_imm(w, rd, rs1, i_imm, rv64, true),
        0x17 => Op::Auipc {
            rd,
            target: rel(xlen, va, sext(w & 0xffff_f000, 32)),
        },
        0x37 => Op::Lui {
            rd,
            imm: sext(w & 0xffff_f000, 32),
        },
        0x23 => match f3 {
            0..=3 if f3 < 3 || rv64 => Op::Store {
                width: match f3 {
                    0 => Width::B,
                    1 => Width::H,
                    2 => Width::W,
                    _ => Width::D,
                },
                rs2,
                rs1,
                off: s_imm,
            },
            _ => Op::Invalid,
        },
        0x27 => match f3 {
            2 | 3 => Op::Float(FOp::Store {
                fmt: if f3 == 2 { Fmt::S } else { Fmt::D },
                rs2: f(w, 20),
                rs1,
                off: s_imm,
            }),
            _ => Op::Unknown,
        },
        0x2f => amo(w, rd, rs1, rs2, rv64),
        0x33 => op_reg(w, rd, rs1, rs2, false),
        0x3b if rv64 => op_reg(w, rd, rs1, rs2, true),
        0x43 | 0x47 | 0x4b | 0x4f => fused(w),
        0x53 => op_fp(w, rv64),
        0x63 => branch(w, va, xlen, rs1, rs2),
        0x67 if f3 == 0 => Op::Jalr {
            rd,
            rs1,
            off: i_imm,
        },
        0x6f => {
            let imm = (field(w, 31, 1) << 20)
                | (field(w, 12, 8) << 12)
                | (field(w, 20, 1) << 11)
                | (field(w, 21, 10) << 1);
            Op::Jal {
                rd,
                target: rel(xlen, va, sext(imm, 21)),
            }
        }
        0x73 => system(w, rd, rs1, f3),
        0x57 | 0x77 | 0x0b | 0x2b | 0x5b | 0x7b => Op::Unknown,
        _ => Op::Invalid,
    }
}

/// Returns the width of an integer load's `funct3`.
///
/// # Arguments
///
/// * `f3` - The field.
/// * `rv64` - Whether the RV64 loads (`ld`, `lwu`) exist.
fn load_width(f3: u32, rv64: bool) -> Option<Width> {
    match f3 {
        0 => Some(Width::B),
        1 => Some(Width::H),
        2 => Some(Width::W),
        3 if rv64 => Some(Width::D),
        4 => Some(Width::Bu),
        5 => Some(Width::Hu),
        6 if rv64 => Some(Width::Wu),
        _ => None,
    }
}

/// Decodes the `OP-IMM` and `OP-IMM-32` groups.
///
/// # Arguments
///
/// * `w` - The word.
/// * `rd` - Its destination.
/// * `rs1` - Its register operand.
/// * `imm` - Its sign-extended immediate.
/// * `rv64` - Whether shift amounts reach 63.
/// * `word` - Whether it is the `OP-IMM-32` group.
fn op_imm(w: u32, rd: Reg, rs1: Reg, imm: i64, rv64: bool, word: bool) -> Op {
    let shamt_bits = if rv64 && !word { 6 } else { 5 };
    let shamt = i64::from(field(w, 20, shamt_bits));
    let high = field(w, 20 + shamt_bits, 12 - shamt_bits) << shamt_bits;
    let (op, imm) = match field(w, 12, 3) {
        0 => (Alu::Add, imm),
        1 if high == 0 => (Alu::Sll, shamt),
        5 if high == 0 => (Alu::Srl, shamt),
        5 if high == 0x400 => (Alu::Sra, shamt),
        2 if !word => (Alu::Slt, imm),
        3 if !word => (Alu::Sltu, imm),
        4 if !word => (Alu::Xor, imm),
        6 if !word => (Alu::Or, imm),
        7 if !word => (Alu::And, imm),
        1 | 5 => return Op::Unknown,
        _ => return Op::Invalid,
    };
    Op::Imm {
        op,
        rd,
        rs1,
        imm,
        word,
    }
}

/// Decodes the `OP` and `OP-32` groups.
///
/// # Arguments
///
/// * `w` - The word.
/// * `rd` - Its destination.
/// * `rs1` - Its left operand.
/// * `rs2` - Its right operand.
/// * `word` - Whether it is the `OP-32` group.
fn op_reg(w: u32, rd: Reg, rs1: Reg, rs2: Reg, word: bool) -> Op {
    let op = match (field(w, 25, 7), field(w, 12, 3)) {
        (0, 0) => Alu::Add,
        (0x20, 0) => Alu::Sub,
        (0, 1) => Alu::Sll,
        (0, 2) if !word => Alu::Slt,
        (0, 3) if !word => Alu::Sltu,
        (0, 4) if !word => Alu::Xor,
        (0, 5) => Alu::Srl,
        (0x20, 5) => Alu::Sra,
        (0, 6) if !word => Alu::Or,
        (0, 7) if !word => Alu::And,
        (1, 0) => Alu::Mul,
        (1, 1) if !word => Alu::Mulh,
        (1, 2) if !word => Alu::Mulhsu,
        (1, 3) if !word => Alu::Mulhu,
        (1, 4) => Alu::Div,
        (1, 5) => Alu::Divu,
        (1, 6) => Alu::Rem,
        (1, 7) => Alu::Remu,
        _ => return Op::Unknown,
    };
    Op::Reg3 {
        op,
        rd,
        rs1,
        rs2,
        word,
    }
}

/// Decodes a conditional branch.
///
/// # Arguments
///
/// * `w` - The word.
/// * `va` - Its address.
/// * `xlen` - The register width.
/// * `rs1` - The left operand.
/// * `rs2` - The right operand.
fn branch(w: u32, va: u64, xlen: Xlen, rs1: Reg, rs2: Reg) -> Op {
    let cond = match field(w, 12, 3) {
        0 => BrCond::Eq,
        1 => BrCond::Ne,
        4 => BrCond::Lt,
        5 => BrCond::Ge,
        6 => BrCond::Ltu,
        7 => BrCond::Geu,
        _ => return Op::Invalid,
    };
    let imm = (field(w, 31, 1) << 12)
        | (field(w, 7, 1) << 11)
        | (field(w, 25, 6) << 5)
        | (field(w, 8, 4) << 1);
    Op::Branch {
        cond,
        rs1,
        rs2,
        target: rel(xlen, va, sext(imm, 13)),
    }
}

/// Decodes the `SYSTEM` group: `ecall`, `ebreak` and the CSR instructions.
///
/// # Arguments
///
/// * `w` - The word.
/// * `rd` - Its destination field.
/// * `rs1` - Its source field.
/// * `f3` - Its `funct3`.
fn system(w: u32, rd: Reg, rs1: Reg, f3: u32) -> Op {
    let csr = crate::num::lo16(u64::from(w >> 20));
    let src = |imm: bool| {
        if imm {
            CsrSrc::Imm(small(w, 15, 5))
        } else {
            CsrSrc::Reg(rs1)
        }
    };
    let op = match f3 {
        0 => {
            return match w >> 7 {
                0 => Op::Ecall,
                0x2000 => Op::Ebreak,
                0x4000 | 0x20_4000 | 0x60_4000 => Op::TrapRet,
                _ => Op::System,
            };
        }
        1 | 5 => CsrOp::Rw,
        2 | 6 => CsrOp::Rs,
        3 | 7 => CsrOp::Rc,
        _ => return Op::Invalid,
    };
    Op::Csr {
        op,
        rd,
        src: src(f3 >= 5),
        csr,
    }
}

/// Decodes the `AMO` group: `lr`, `sc` and the atomic operations.
///
/// # Arguments
///
/// * `w` - The word.
/// * `rd` - Its destination.
/// * `rs1` - Its address register.
/// * `rs2` - Its operand.
/// * `rv64` - Whether the doubleword forms exist.
fn amo(w: u32, rd: Reg, rs1: Reg, rs2: Reg, rv64: bool) -> Op {
    let width = match field(w, 12, 3) {
        2 => Width::W,
        3 if rv64 => Width::D,
        _ => return Op::Invalid,
    };
    let order = small(w, 25, 2);
    let op = match field(w, 27, 5) {
        0x02 if field(w, 20, 5) == 0 => {
            return Op::Lr {
                width,
                rd,
                rs1,
                order,
            };
        }
        0x03 => {
            return Op::Sc {
                width,
                rd,
                rs1,
                rs2,
                order,
            };
        }
        0x01 => AmoOp::Swap,
        0x00 => AmoOp::Add,
        0x04 => AmoOp::Xor,
        0x0c => AmoOp::And,
        0x08 => AmoOp::Or,
        0x10 => AmoOp::Min,
        0x14 => AmoOp::Max,
        0x18 => AmoOp::Minu,
        0x1c => AmoOp::Maxu,
        _ => return Op::Unknown,
    };
    Op::Amo {
        op,
        width,
        rd,
        rs1,
        rs2,
        order,
    }
}

/// Returns the float format a two-bit `fmt` field names.
///
/// # Arguments
///
/// * `v` - The field.
///
/// # Returns
///
/// `S` or `D`; `None` for half and quad precision, which the engine does
/// not model.
fn fmt_of(v: u32) -> Option<Fmt> {
    match v {
        0 => Some(Fmt::S),
        1 => Some(Fmt::D),
        _ => None,
    }
}

/// Decodes a fused multiply-add.
///
/// # Arguments
///
/// * `w` - The word.
fn fused(w: u32) -> Op {
    let Some(fmt) = fmt_of(field(w, 25, 2)) else {
        return Op::Unknown;
    };
    let op = match field(w, 2, 2) {
        0 => Fused::Madd,
        1 => Fused::Msub,
        2 => Fused::Nmsub,
        _ => Fused::Nmadd,
    };
    Op::Float(FOp::Fused {
        op,
        fmt,
        rd: f(w, 7),
        rs1: f(w, 15),
        rs2: f(w, 20),
        rs3: f(w, 27),
        rm: small(w, 12, 3),
    })
}

/// Decodes the `OP-FP` group.
///
/// # Arguments
///
/// * `w` - The word.
/// * `rv64` - Whether the doubleword integer conversions and `fmv.x.d`
///   exist.
fn op_fp(w: u32, rv64: bool) -> Op {
    let Some(fmt) = fmt_of(field(w, 25, 2)) else {
        return Op::Unknown;
    };
    let (rd, rs1, rs2) = (f(w, 7), f(w, 15), f(w, 20));
    let (xd, xs1) = (x(w, 7), x(w, 15));
    let rm = small(w, 12, 3);
    let f3 = field(w, 12, 3);
    let sel = field(w, 20, 5);
    let int = match sel {
        0 => Some(IntFmt::W),
        1 => Some(IntFmt::Wu),
        2 if rv64 => Some(IntFmt::L),
        3 if rv64 => Some(IntFmt::Lu),
        _ => None,
    };
    let arith = |op| {
        Op::Float(FOp::Arith {
            op,
            fmt,
            rd,
            rs1,
            rs2,
            rm,
        })
    };
    match (field(w, 27, 5), f3) {
        (0x00, _) => arith(FArith::Add),
        (0x01, _) => arith(FArith::Sub),
        (0x02, _) => arith(FArith::Mul),
        (0x03, _) => arith(FArith::Div),
        (0x0b, _) if sel == 0 => Op::Float(FOp::Sqrt { fmt, rd, rs1, rm }),
        (0x04, 0) => arith(FArith::Sgnj),
        (0x04, 1) => arith(FArith::Sgnjn),
        (0x04, 2) => arith(FArith::Sgnjx),
        (0x05, 0) => arith(FArith::Min),
        (0x05, 1) => arith(FArith::Max),
        (0x08, _) => match (fmt, sel) {
            (Fmt::S, 1) => Op::Float(FOp::Convert {
                from: Fmt::D,
                to: Fmt::S,
                rd,
                rs1,
                rm,
            }),
            (Fmt::D, 0) => Op::Float(FOp::Convert {
                from: Fmt::S,
                to: Fmt::D,
                rd,
                rs1,
                rm,
            }),
            _ => Op::Unknown,
        },
        (0x14, 0..=2) => Op::Float(FOp::Cmp {
            op: match f3 {
                0 => FCmp::Le,
                1 => FCmp::Lt,
                _ => FCmp::Eq,
            },
            fmt,
            rd: xd,
            rs1,
            rs2,
        }),
        (0x18, _) => int.map_or(Op::Unknown, |int| {
            Op::Float(FOp::ToInt {
                fmt,
                int,
                rd: xd,
                rs1,
                rm,
            })
        }),
        (0x1a, _) => int.map_or(Op::Unknown, |int| {
            Op::Float(FOp::FromInt {
                fmt,
                int,
                rd,
                rs1: xs1,
                rm,
            })
        }),
        (0x1c, 0) if sel == 0 && (fmt == Fmt::S || rv64) => {
            Op::Float(FOp::MvToInt { fmt, rd: xd, rs1 })
        }
        (0x1c, 1) if sel == 0 => Op::Float(FOp::Class { fmt, rd: xd, rs1 }),
        (0x1e, 0) if sel == 0 && (fmt == Fmt::S || rv64) => {
            Op::Float(FOp::MvFromInt { fmt, rd, rs1: xs1 })
        }
        _ => Op::Unknown,
    }
}
