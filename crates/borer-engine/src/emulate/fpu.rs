//! The x87 floating-point unit: its stack, its 80-bit memory format and
//! the arithmetic the emulator models.

use super::sse::Rounding;
use super::{Emulator, Stop, sign_extend, width_bits};
use crate::isa::x86::{Instruction, Mnemonic, OpKind, st_depth_mod8};
use crate::num::{lo16, lo32};

/// What the memory operand of an x87 instruction holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FpuOperand {
    /// A signed integer of the operand's width: `fild`, `fist`, `fiadd`
    /// and kin.
    Integer,
    /// A single or a double: `fld`, `fst`, `fadd` and kin.
    Float,
}

impl FpuOperand {
    /// What the memory operand of an x87 mnemonic holds.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    pub(super) fn of(m: Mnemonic) -> FpuOperand {
        match m {
            Mnemonic::Fild
            | Mnemonic::Fist
            | Mnemonic::Fistp
            | Mnemonic::Fisttp
            | Mnemonic::Fiadd
            | Mnemonic::Fisub
            | Mnemonic::Fisubr
            | Mnemonic::Fimul
            | Mnemonic::Fidiv
            | Mnemonic::Fidivr => FpuOperand::Integer,
            _ => FpuOperand::Float,
        }
    }
}

/// What an x87 arithmetic instruction computes between `st(dst)` and its
/// operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FpuArith {
    /// `fadd`, `faddp`, `fiadd`.
    Add,
    /// `fsub`, `fsubp`, `fisub`.
    Sub,
    /// `fsubr`, `fsubrp`, `fisubr`: the operand minus `st(dst)`, which is
    /// the whole reason the reversed forms exist.
    SubReversed,
    /// `fmul`, `fmulp`, `fimul`.
    Mul,
    /// `fdiv`, `fdivp`, `fidiv`.
    Div,
    /// `fdivr`, `fdivrp`, `fidivr`: the operand over `st(dst)`.
    DivReversed,
}

impl FpuArith {
    /// The operation a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The operation, or `None` when `m` is not x87 arithmetic.
    pub(super) fn of(m: Mnemonic) -> Option<FpuArith> {
        Some(match m {
            Mnemonic::Fadd | Mnemonic::Faddp | Mnemonic::Fiadd => FpuArith::Add,
            Mnemonic::Fsub | Mnemonic::Fsubp | Mnemonic::Fisub => FpuArith::Sub,
            Mnemonic::Fsubr | Mnemonic::Fsubrp | Mnemonic::Fisubr => FpuArith::SubReversed,
            Mnemonic::Fmul | Mnemonic::Fmulp | Mnemonic::Fimul => FpuArith::Mul,
            Mnemonic::Fdiv | Mnemonic::Fdivp | Mnemonic::Fidiv => FpuArith::Div,
            Mnemonic::Fdivr | Mnemonic::Fdivrp | Mnemonic::Fidivr => FpuArith::DivReversed,
            _ => return None,
        })
    }

    /// Applies the operation.
    ///
    /// # Arguments
    ///
    /// * `lhs` - `st(dst)`.
    /// * `rhs` - The operand.
    pub(super) fn apply(self, lhs: f64, rhs: f64) -> f64 {
        match self {
            FpuArith::Add => lhs + rhs,
            FpuArith::Sub => lhs - rhs,
            FpuArith::SubReversed => rhs - lhs,
            FpuArith::Mul => lhs * rhs,
            FpuArith::Div => lhs / rhs,
            FpuArith::DivReversed => rhs / lhs,
        }
    }
}

/// Whether an x87 instruction pops the stack after its work: the `p`
/// forms, and `fisttp`, which always pops after its truncating store.
///
/// # Arguments
///
/// * `m` - The mnemonic.
fn fpu_pops(m: Mnemonic) -> bool {
    matches!(
        m,
        Mnemonic::Fstp
            | Mnemonic::Fistp
            | Mnemonic::Fisttp
            | Mnemonic::Faddp
            | Mnemonic::Fsubp
            | Mnemonic::Fsubrp
            | Mnemonic::Fmulp
            | Mnemonic::Fdivp
            | Mnemonic::Fdivrp
    )
}

/// The magnitude from which `fsincos` and `fptan` take no operand: 2^63.
pub(super) const FPU_TRIG_RANGE: f64 = 9_223_372_036_854_775_808.0;

/// Bytes of the x87 extended format: an eighty-bit value.
pub(super) const EXTENDED_BYTES: usize = 10;

/// Bias of the extended format's fifteen-bit exponent.
const EXTENDED_BIAS: i64 = 16383;

/// The extended exponent field of an infinity or a NaN.
const EXTENDED_SPECIAL: u16 = 0x7fff;

/// Bias of a double's eleven-bit exponent.
const DOUBLE_BIAS: i64 = 1023;

/// The double nearest an x87 extended value.
///
/// The format is a sign, a fifteen-bit exponent biased by
/// [`EXTENDED_BIAS`] and a 64-bit mantissa whose top bit is the explicit
/// integer bit. The mantissa rounds to the double's 53 bits, to nearest
/// even, and the exponent then scales it, so a magnitude past a double
/// overflows to an infinity and one below its denormals underflows to
/// zero. A zero exponent is a denormal, scaled as the exponent one. The
/// special exponent is an infinity when the fraction is clear and a NaN
/// otherwise.
///
/// # Arguments
///
/// * `mantissa` - The low eight bytes.
/// * `high` - The top two, in the low sixteen bits: the sign bit over the
///   exponent.
pub(super) fn extended_to_f64(mantissa: u64, high: u64) -> f64 {
    let high = lo16(high);
    let exponent = high & EXTENDED_SPECIAL;
    let magnitude = if exponent == EXTENDED_SPECIAL {
        if mantissa << 1 == 0 {
            f64::INFINITY
        } else {
            f64::NAN
        }
    } else {
        #[expect(
            clippy::cast_precision_loss,
            reason = "the 64-bit mantissa rounds to the double's 53 bits, which is the conversion"
        )]
        let rounded = mantissa as f64;
        scale(rounded, i64::from(exponent.max(1)) - EXTENDED_BIAS - 63)
    };
    if high & 0x8000 == 0 {
        magnitude
    } else {
        -magnitude
    }
}

/// `v` times two to the `e`.
///
/// Multiplying by a power of two is exact while the result is a normal
/// double, so only the step that leaves that range rounds. The exponent is
/// applied in the steps a double's own exponent can hold.
///
/// # Arguments
///
/// * `v` - The value.
/// * `e` - The binary exponent, of any size.
pub(super) fn scale(v: f64, e: i64) -> f64 {
    let (mut v, mut e) = (v, e);
    while e != 0 {
        let step = e.clamp(1 - DOUBLE_BIAS, DOUBLE_BIAS);
        v *= f64::from_bits((step + DOUBLE_BIAS).cast_unsigned() << 52);
        e -= step;
    }
    v
}

/// An x87 extended value equal to a double.
///
/// Exact, since the extended format holds every double: a denormal is
/// normalized under its explicit integer bit, and an infinity or a NaN
/// keeps its fraction under the special exponent.
///
/// # Arguments
///
/// * `v` - The value.
///
/// # Returns
///
/// The low eight bytes and the top two, as [`extended_to_f64`] takes them.
pub(super) fn f64_to_extended(v: f64) -> (u64, u64) {
    let bits = v.to_bits();
    let sign = (bits >> 63) << 15;
    let fraction = bits & ((1 << 52) - 1);
    let exponent = i64::from(lo16(bits >> 52) & 0x7ff);
    let normal = 1 << 63 | fraction << 11;
    let (mantissa, exponent) = match exponent {
        0 if fraction == 0 => (0, 0),
        0 => {
            let unnormal = fraction << 11;
            let shift = unnormal.leading_zeros();
            (
                unnormal << shift,
                1 + EXTENDED_BIAS - DOUBLE_BIAS - i64::from(shift),
            )
        }
        0x7ff => (normal, i64::from(EXTENDED_SPECIAL)),
        e => (normal, e + EXTENDED_BIAS - DOUBLE_BIAS),
    };
    (mantissa, sign | exponent.cast_unsigned())
}

impl Emulator<'_> {
    /// Reads `st(n)`.
    ///
    /// # Arguments
    ///
    /// * `n` - Depth from the top of the stack.
    pub(super) fn st(&self, n: usize) -> f64 {
        self.fpu
            .get((self.fpu_top + n) % self.fpu.len())
            .copied()
            .unwrap_or(0.0)
    }

    /// Writes `st(n)`.
    ///
    /// # Arguments
    ///
    /// * `n` - Depth from the top of the stack.
    /// * `v` - The value.
    pub(super) fn set_st(&mut self, n: usize, v: f64) {
        let at = (self.fpu_top + n) % self.fpu.len();
        if let Some(slot) = self.fpu.get_mut(at) {
            *slot = v;
        }
    }

    /// Pushes a value, which moves the top down as the hardware does.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    pub(super) fn fpush(&mut self, v: f64) {
        self.fpu_top = (self.fpu_top + self.fpu.len() - 1) % self.fpu.len();
        self.set_st(0, v);
    }

    /// Pops the top of the stack, discarding it.
    fn fpop(&mut self) {
        self.set_st(0, 0.0);
        self.fpu_top = (self.fpu_top + 1) % self.fpu.len();
    }

    /// Reads the memory operand of an x87 instruction as a double.
    ///
    /// The hardware keeps eighty-bit values; this keeps doubles, which is
    /// exact for every integer these routines load and enough for the
    /// rest, and the difference cannot reach an address or a byte of
    /// recovered text. An integer operand is a word, a dword or a qword,
    /// sign-extended; a float operand is a single, a double or the
    /// eighty-bit extended format, which [`extended_to_f64`] rounds.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `operand` - What the memory holds.
    ///
    /// # Errors
    ///
    /// A fault when the operand is unmapped.
    fn fpu_memory(&self, i: &Instruction, operand: FpuOperand) -> Result<f64, Stop> {
        let addr = self.mem_addr(i)?;
        let width = i.memory_size().size();
        Ok(match operand {
            FpuOperand::Integer => {
                let width = width.clamp(2, 8);
                #[expect(
                    clippy::cast_precision_loss,
                    reason = "fild and its kin round the integer to the double this keeps for an x87 value"
                )]
                let loaded = sign_extend(self.load(addr, width)?, width_bits(width)) as f64;
                loaded
            }
            FpuOperand::Float if width == EXTENDED_BYTES => {
                extended_to_f64(self.load(addr, 8)?, self.load(addr.wrapping_add(8), 2)?)
            }
            FpuOperand::Float if width == 4 => f64::from(f32::from_bits(lo32(self.load(addr, 4)?))),
            FpuOperand::Float => f64::from_bits(self.load(addr, 8)?),
        })
    }

    /// `fld` and `fild`: pushes `st(n)`, a float or an integer from memory.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    ///
    /// # Errors
    ///
    /// A fault when the operand is unmapped.
    pub(super) fn fpu_load(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let v = if i.op0_kind() == OpKind::Register {
            self.st(st_depth_mod8(i.op0_register()))
        } else {
            self.fpu_memory(i, FpuOperand::of(m))?
        };
        self.fpush(v);
        Ok(None)
    }

    /// `fst`, `fstp`, `fist`, `fistp` and `fisttp`: `st(0)` into `st(n)`,
    /// or into memory as a float or an integer, popping for the `p` forms.
    ///
    /// An integer store takes the operand's own width (a word, a dword or
    /// a qword) and rounds the way the control word says, to nearest even
    /// by default; only `fisttp` truncates. A value the width cannot hold
    /// is the integer indefinite, as for `cvtsd2si`. A float store is a
    /// single, a double or the eighty-bit extended format, which
    /// [`f64_to_extended`] writes exactly.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    ///
    /// # Errors
    ///
    /// [`Stop::MemoryFull`] when the store would take memory past its cap;
    /// the write cannot fault.
    pub(super) fn fpu_store(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let v = self.st(0);
        if i.op0_kind() == OpKind::Register {
            self.set_st(st_depth_mod8(i.op0_register()), v);
        } else {
            let addr = self.mem_addr(i)?;
            let width = i.memory_size().size();
            if FpuOperand::of(m) == FpuOperand::Integer {
                let size = width.clamp(2, 8);
                let rounding = if m == Mnemonic::Fisttp {
                    Rounding::Truncate
                } else {
                    Rounding::Nearest
                };
                self.write(
                    addr,
                    super::sse::float_to_int(v, width_bits(size), rounding),
                    size,
                )?;
            } else if width == EXTENDED_BYTES {
                let (mantissa, high) = f64_to_extended(v);
                self.write(addr, mantissa, 8)?;
                self.write(addr.wrapping_add(8), high, 2)?;
            } else if width == 4 {
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "fst to a single rounds the double by design"
                )]
                let single = v as f32;
                self.write(addr, u64::from(single.to_bits()), 4)?;
            } else {
                self.write(addr, v.to_bits(), 8)?;
            }
        }
        if fpu_pops(m) {
            self.fpop();
        }
        Ok(None)
    }

    /// The x87 arithmetic: `st(dst)` and an operand combined by `op`.
    ///
    /// The operand is `st(n)` when it is a register, else memory holding
    /// an integer for the `fi` forms and a float otherwise; the destination
    /// is `st(0)` unless the instruction names another.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    /// * `op` - What it computes.
    ///
    /// # Errors
    ///
    /// A fault when a memory operand is unmapped.
    pub(super) fn fpu_arith(
        &mut self,
        i: &Instruction,
        m: Mnemonic,
        op: FpuArith,
    ) -> Result<Option<u64>, Stop> {
        let (dst, rhs) = if i.op_count() == 0 {
            (0usize, self.st(1))
        } else if i.op0_kind() == OpKind::Register {
            let a = st_depth_mod8(i.op0_register());
            if i.op_count() > 1 && i.op_kind(1) == OpKind::Register {
                let b = st_depth_mod8(i.op_register(1));
                if a == 0 {
                    (0, self.st(b))
                } else {
                    (a, self.st(0))
                }
            } else {
                (0, self.st(a))
            }
        } else {
            (0, self.fpu_memory(i, FpuOperand::of(m))?)
        };
        let v = op.apply(self.st(dst), rhs);
        self.set_st(dst, v);
        if fpu_pops(m) {
            self.fpop();
        }
        Ok(None)
    }
}
