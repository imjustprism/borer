//! SSE and AVX vector instructions: scalar and packed floating point,
//! conversions and compares, and the packed integer operations string and
//! hash routines are built from.
//!
//! The 128-bit forms run the models below; the 256-bit forms whose two
//! 128-bit halves compute independently run as lane pairs over them, and
//! the ones that cross the boundary between the halves (the cross-lane
//! shuffles, inserts and gathers) stay unmodeled.
//!
//! Measured over eight Windows binaries after the integer instructions were
//! modeled, these were what stopped the emulator: a C runtime's `strlen`
//! compares sixteen bytes at a time (`pcmpeqb`, `pmovmskb`), and any code
//! that touches a `double` does its math in the low lane of an `xmm`
//! register. Floating point runs on the host's IEEE arithmetic, which
//! rounds to nearest-even as the default `MXCSR` does; the rounding mode is
//! not modeled.

use super::{Emulator, Stop, lane_bits, lo64, mask, packed, reg_bits, sign_extend, ymm_index};
use crate::isa::x86::{Instruction, Mnemonic, OpKind, xmm_slot};
use crate::num::lo32;

/// `MXCSR` as the process starts: every exception masked, round to nearest.
const MXCSR_DEFAULT: u64 = 0x1f80;

/// The low lane of a 128-bit value, `bytes` wide.
fn lane(bytes: usize) -> u128 {
    if bytes == 8 {
        u128::from(u64::MAX)
    } else {
        0xffff_ffff
    }
}

/// The width of a scalar lane: a single or a double, or the dword or
/// qword an integer move carries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Width {
    /// Four bytes.
    Single,
    /// Eight bytes.
    Double,
}

impl Width {
    /// The lane a scalar move carries: four bytes for `movss` and `movd`,
    /// eight for `movsd` and `movq`, and the VEX forms alike.
    ///
    /// # Arguments
    ///
    /// * `m` - The move's mnemonic.
    pub(super) fn of_scalar(m: Mnemonic) -> Width {
        match m {
            Mnemonic::Movss | Mnemonic::Movd | Mnemonic::Vmovss | Mnemonic::Vmovd => Width::Single,
            _ => Width::Double,
        }
    }

    /// The lane in bytes.
    const fn bytes(self) -> usize {
        match self {
            Width::Single => 4,
            Width::Double => 8,
        }
    }

    /// The lane in bits.
    const fn bits(self) -> u32 {
        match self {
            Width::Single => 32,
            Width::Double => 64,
        }
    }

    /// The low lane of a 128-bit value.
    pub(super) fn lane(self) -> u128 {
        lane(self.bytes())
    }

    /// The value a lane's bits hold, as a double.
    ///
    /// # Arguments
    ///
    /// * `raw` - The lane's bits.
    fn to_f64(self, raw: u64) -> f64 {
        match self {
            Width::Single => f64::from(f32::from_bits(lo32(raw))),
            Width::Double => f64::from_bits(raw),
        }
    }
}

/// How a float becomes an integer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Rounding {
    /// Toward zero: the `cvtt*` conversions and `fisttp`.
    Truncate,
    /// To the nearest, ties to even: the default `MXCSR` and x87 control
    /// word.
    Nearest,
}

/// A scalar operation on doubles or singles, given as bit patterns.
///
/// # Arguments
///
/// * `m` - The mnemonic, legacy or VEX.
/// * `a` - The first operand's lane.
/// * `b` - The second operand's lane.
/// * `width` - Whether the lanes are singles or doubles.
///
/// # Returns
///
/// The result's bits, or `None` when `m` is not an arithmetic operation.
fn arith(m: Mnemonic, a: u64, b: u64, width: Width) -> Option<u64> {
    use Mnemonic as M;
    macro_rules! op {
        ($t:ty, $from:expr, $to:expr) => {{
            let (x, y): ($t, $t) = ($from(a), $from(b));
            let r: $t = match m {
                M::Addsd
                | M::Addss
                | M::Addpd
                | M::Addps
                | M::Vaddsd
                | M::Vaddss
                | M::Vaddpd
                | M::Vaddps => x + y,
                M::Subsd
                | M::Subss
                | M::Subpd
                | M::Subps
                | M::Vsubsd
                | M::Vsubss
                | M::Vsubpd
                | M::Vsubps => x - y,
                M::Mulsd
                | M::Mulss
                | M::Mulpd
                | M::Mulps
                | M::Vmulsd
                | M::Vmulss
                | M::Vmulpd
                | M::Vmulps => x * y,
                M::Divsd
                | M::Divss
                | M::Divpd
                | M::Divps
                | M::Vdivsd
                | M::Vdivss
                | M::Vdivpd
                | M::Vdivps => x / y,
                M::Minsd | M::Minss | M::Minpd | M::Minps | M::Vminsd | M::Vminss => {
                    if x < y {
                        x
                    } else {
                        y
                    }
                }
                M::Maxsd | M::Maxss | M::Maxpd | M::Maxps | M::Vmaxsd | M::Vmaxss => {
                    if x > y {
                        x
                    } else {
                        y
                    }
                }
                M::Sqrtsd | M::Sqrtss | M::Sqrtpd | M::Sqrtps | M::Vsqrtsd | M::Vsqrtss => y.sqrt(),
                _ => return None,
            };
            Some($to(r))
        }};
    }
    match width {
        Width::Double => op!(f64, f64::from_bits, f64::to_bits),
        Width::Single => op!(f32, |v: u64| f32::from_bits(lo32(v)), |r: f32| u64::from(
            r.to_bits()
        )),
    }
}

/// A float converted to an integer of `bits`; a NaN or a value out of
/// range is the "integer indefinite", the lowest value of the width.
///
/// # Arguments
///
/// * `x` - The float.
/// * `bits` - The integer's width.
/// * `rounding` - How the fraction goes.
pub(super) fn float_to_int(x: f64, bits: u32, rounding: Rounding) -> u64 {
    let r = match rounding {
        Rounding::Truncate => x.trunc(),
        Rounding::Nearest => x.round_ties_even(),
    };
    let top = 2f64.powi(bits.cast_signed() - 1);
    if r.is_nan() || r < -top || r >= top {
        return 1u64 << (bits - 1);
    }
    #[expect(
        clippy::cast_possible_truncation,
        reason = "the range check above keeps `r` within the width, so it converts exactly"
    )]
    let int = r as i64;
    mask(int.cast_unsigned(), bits)
}

impl Emulator<'_> {
    /// Reads operand `n` as a scalar lane: the low `bytes` of an `xmm`
    /// register, or exactly `bytes` of memory, so a double at the end of a
    /// buffer is read without the eight bytes after it.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn lane_operand(&mut self, i: &Instruction, n: u32, bytes: usize) -> Result<u64, Stop> {
        match i.op_kind(n) {
            OpKind::Register if xmm_slot(i.op_register(n)).is_some() => {
                Ok(lo64(self.vector_operand(i, n)? & lane(bytes)))
            }
            OpKind::Memory => {
                let at = self.mem_addr(i)?;
                self.load(at, bytes)
            }
            _ => self
                .operand(i, n)
                .map(|v| mask(v, u32::try_from(bytes * 8).unwrap_or(64))),
        }
    }

    /// The operands of a vector operation: for the two-operand legacy form
    /// the destination and the source, for the VEX form its two sources.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn sources(&mut self, i: &Instruction) -> Result<(u128, u128), Stop> {
        if i.op_count() >= 3 {
            Ok((self.vector_operand(i, 1)?, self.vector_operand(i, 2)?))
        } else {
            Ok((self.vector_operand(i, 0)?, self.vector_operand(i, 1)?))
        }
    }

    /// Runs `m` when it is an SSE or AVX instruction this module models.
    ///
    /// # Returns
    ///
    /// `None` when `m` is not one, so the caller reports it unmodeled: a
    /// `zmm` form, or a 256-bit form whose halves do not compute
    /// independently (the cross-lane shuffles and inserts), which only a
    /// full 256-bit model could answer.
    pub(super) fn vector_op(
        &mut self,
        i: &Instruction,
        m: Mnemonic,
    ) -> Option<Result<Option<u64>, Stop>> {
        let vector = |n: u32| i.op_kind(n) == OpKind::Register;
        if (0..i.op_count()).any(|n| vector(n) && i.op_register(n).is_zmm()) {
            return None;
        }
        if (0..i.op_count()).any(|n| vector(n) && i.op_register(n).is_ymm()) {
            return self.ymm_pair(i, m).map(|run| run.map(|()| None));
        }
        let run = match m {
            Mnemonic::Vzeroupper => Ok(()),
            Mnemonic::Stmxcsr | Mnemonic::Vstmxcsr => self.store(i, MXCSR_DEFAULT),
            Mnemonic::Ldmxcsr | Mnemonic::Vldmxcsr => Ok(()),
            _ => self.vector_step(i, m)?,
        };
        Some(run.map(|()| None))
    }

    /// A 256-bit instruction whose two 128-bit halves compute
    /// independently, run as lane pairs over the 128-bit models.
    ///
    /// The `ymm` registers are the `xmm` registers plus an upper half
    /// ([`Emulator::ymm_hi`]), and each instruction here is one whose
    /// 256-bit form is exactly its 128-bit form run on each half: the
    /// aligned and unaligned moves, the bitwise logic, and the packed
    /// integer add and subtract. An instruction that moves lanes across
    /// the boundary does not belong here and stays unmodeled. A memory
    /// operand moves the low lane alone, the width the decompiler's
    /// expression tree models a ymm access at, so the upper halves ride
    /// along in registers only.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction, with at least one `ymm` register operand.
    /// * `m` - Its mnemonic.
    ///
    /// # Returns
    ///
    /// `None` when the instruction is not one of these, so the caller
    /// reports it unmodeled.
    fn ymm_pair(&mut self, i: &Instruction, m: Mnemonic) -> Option<Result<(), Stop>> {
        use Mnemonic as M;
        let lane_pairs = matches!(
            m,
            M::Vmovdqa
                | M::Vmovdqu
                | M::Vmovaps
                | M::Vmovups
                | M::Vmovapd
                | M::Vmovupd
                | M::Vpand
                | M::Vpandn
                | M::Vpor
                | M::Vpxor
                | M::Vandps
                | M::Vandpd
                | M::Vandnps
                | M::Vandnpd
                | M::Vorps
                | M::Vorpd
                | M::Vxorps
                | M::Vxorpd
                | M::Vpaddb
                | M::Vpaddw
                | M::Vpaddd
                | M::Vpaddq
                | M::Vpsubb
                | M::Vpsubw
                | M::Vpsubd
                | M::Vpsubq
        );
        lane_pairs.then(|| self.ymm_step(i, m))
    }

    /// The body of [`Emulator::ymm_pair`], once the instruction is known to
    /// be one whose halves compute independently.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn ymm_step(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        use Mnemonic as M;
        match m {
            M::Vmovdqa | M::Vmovdqu | M::Vmovaps | M::Vmovups | M::Vmovapd | M::Vmovupd => {
                let (lo, hi) = self.wide_operand(i, 1)?;
                self.wide_store(i, lo, hi)
            }
            M::Vpand
            | M::Vpandn
            | M::Vpor
            | M::Vpxor
            | M::Vandps
            | M::Vandpd
            | M::Vandnps
            | M::Vandnpd
            | M::Vorps
            | M::Vorpd
            | M::Vxorps
            | M::Vxorpd => {
                let ((al, ah), (bl, bh)) = (self.wide_operand(i, 1)?, self.wide_operand(i, 2)?);
                let f = match m {
                    M::Vpandn | M::Vandnps | M::Vandnpd => |a: u128, b: u128| !a & b,
                    M::Vpor | M::Vorps | M::Vorpd => |a: u128, b: u128| a | b,
                    M::Vpxor | M::Vxorps | M::Vxorpd => |a: u128, b: u128| a ^ b,
                    _ => |a: u128, b: u128| a & b,
                };
                self.wide_store(i, f(al, bl), f(ah, bh))
            }
            _ => {
                let ((al, ah), (bl, bh)) = (self.wide_operand(i, 1)?, self.wide_operand(i, 2)?);
                let bits = lane_bits(m);
                let sub = matches!(m, M::Vpsubb | M::Vpsubw | M::Vpsubd | M::Vpsubq);
                let lane_op = |a: u128, b: u128| {
                    if sub {
                        packed(a, b, bits, u64::wrapping_sub)
                    } else {
                        packed(a, b, bits, u64::wrapping_add)
                    }
                };
                self.wide_store(i, lane_op(al, bl), lane_op(ah, bh))
            }
        }
    }

    /// Reads operand `n` as the two 128-bit halves of a 256-bit value: an
    /// `ymm` register's low and upper halves, or the low 128 bits of memory.
    ///
    /// The decompiler's expression tree caps a vector access at 128 bits
    /// (`expr::Ty` has no 256-bit type), and the block verifier requires
    /// the emulator to write only what a lifted store covers, so a ymm
    /// memory access moves the low lane alone and reads the upper half as
    /// zero; the upper halves ride along in registers.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `n` - The operand index.
    ///
    /// # Errors
    ///
    /// When the operand is neither an `ymm` register nor memory.
    fn wide_operand(&mut self, i: &Instruction, n: u32) -> Result<(u128, u128), Stop> {
        match i.op_kind(n) {
            OpKind::Register => match ymm_index(i.op_register(n)) {
                Some(k) => Ok((self.xmm[k], self.ymm_hi[k])),
                None => Err(Stop::Unmodeled(format!("vector {:?}", i.op_register(n)))),
            },
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                let lo = u128::from(self.load(addr, 8)?)
                    | u128::from(self.load(addr.wrapping_add(8), 8)?) << 64;
                Ok((lo, 0))
            }
            other => Err(Stop::Unmodeled(format!("vector operand {other:?}"))),
        }
    }

    /// Writes the two 128-bit halves to operand 0: an `ymm` register's low
    /// and upper halves, or the low half to memory, sixteen bytes of it.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `lo` - The low half.
    /// * `hi` - The upper half, kept by a register destination and dropped
    ///   by a memory one, as [`Emulator::wide_operand`] reads it.
    ///
    /// # Errors
    ///
    /// When operand 0 is neither an `ymm` register nor memory, or memory
    /// would grow past its cap.
    fn wide_store(&mut self, i: &Instruction, lo: u128, hi: u128) -> Result<(), Stop> {
        match i.op0_kind() {
            OpKind::Register => match ymm_index(i.op0_register()) {
                Some(k) => {
                    self.xmm[k] = lo;
                    self.ymm_hi[k] = hi;
                    Ok(())
                }
                None => Err(Stop::Unmodeled(format!("vector {:?}", i.op0_register()))),
            },
            OpKind::Memory => {
                let addr = self.mem_addr(i)?;
                self.write(addr, lo64(lo), 8)?;
                self.write(addr.wrapping_add(8), lo64(lo >> 64), 8)
            }
            other => Err(Stop::Unmodeled(format!("vector store {other:?}"))),
        }
    }

    /// The body of [`Emulator::vector_op`], by family.
    fn vector_step(&mut self, i: &Instruction, m: Mnemonic) -> Option<Result<(), Stop>> {
        use Mnemonic as M;
        Some(match m {
            M::Addsd
            | M::Subsd
            | M::Mulsd
            | M::Divsd
            | M::Minsd
            | M::Maxsd
            | M::Sqrtsd
            | M::Vaddsd
            | M::Vsubsd
            | M::Vmulsd
            | M::Vdivsd
            | M::Vminsd
            | M::Vmaxsd
            | M::Vsqrtsd => self.scalar_float(i, m, Width::Double),
            M::Addss
            | M::Subss
            | M::Mulss
            | M::Divss
            | M::Minss
            | M::Maxss
            | M::Sqrtss
            | M::Vaddss
            | M::Vsubss
            | M::Vmulss
            | M::Vdivss
            | M::Vminss
            | M::Vmaxss
            | M::Vsqrtss => self.scalar_float(i, m, Width::Single),
            M::Addpd
            | M::Subpd
            | M::Mulpd
            | M::Divpd
            | M::Minpd
            | M::Maxpd
            | M::Sqrtpd
            | M::Vaddpd
            | M::Vsubpd
            | M::Vmulpd
            | M::Vdivpd => self.packed_float(i, m, Width::Double),
            M::Addps
            | M::Subps
            | M::Mulps
            | M::Divps
            | M::Minps
            | M::Maxps
            | M::Sqrtps
            | M::Vaddps
            | M::Vsubps
            | M::Vmulps
            | M::Vdivps => self.packed_float(i, m, Width::Single),
            M::Cmpss | M::Vcmpss => self.scalar_cmp(i, Width::Single),
            M::Cmpsd | M::Vcmpsd
                if i.op0_kind() == OpKind::Register && i.op0_register().is_vector_register() =>
            {
                self.scalar_cmp(i, Width::Double)
            }
            M::Comisd | M::Ucomisd | M::Vcomisd | M::Vucomisd => {
                self.float_compare(i, Width::Double)
            }
            M::Comiss | M::Ucomiss | M::Vcomiss | M::Vucomiss => {
                self.float_compare(i, Width::Single)
            }
            M::Cvtsi2sd | M::Cvtsi2ss | M::Vcvtsi2sd | M::Vcvtsi2ss => self.int_to_float(i, m),
            M::Cvttsd2si | M::Vcvttsd2si => self.float_to_int(i, Width::Double, Rounding::Truncate),
            M::Cvtsd2si | M::Vcvtsd2si => self.float_to_int(i, Width::Double, Rounding::Nearest),
            M::Cvttss2si | M::Vcvttss2si => self.float_to_int(i, Width::Single, Rounding::Truncate),
            M::Cvtss2si | M::Vcvtss2si => self.float_to_int(i, Width::Single, Rounding::Nearest),
            M::Cvtss2sd | M::Cvtsd2ss | M::Vcvtss2sd | M::Vcvtsd2ss => self.float_width(i, m),
            M::Cvtdq2pd | M::Cvtdq2ps | M::Cvttps2dq | M::Cvtps2pd | M::Cvtpd2ps | M::Cvttpd2dq => {
                self.packed_convert(i, m)
            }
            M::Andps
            | M::Andpd
            | M::Andnps
            | M::Andnpd
            | M::Orps
            | M::Orpd
            | M::Xorps
            | M::Xorpd
            | M::Pand
            | M::Pandn
            | M::Por
            | M::Pxor
            | M::Vandps
            | M::Vandpd
            | M::Vandnps
            | M::Vandnpd
            | M::Vorps
            | M::Vorpd
            | M::Vxorps
            | M::Vxorpd
            | M::Vpand
            | M::Vpandn
            | M::Vpor
            | M::Vpxor => self.logic(i, m),
            M::Pcmpeqb
            | M::Pcmpeqw
            | M::Pcmpeqd
            | M::Pcmpeqq
            | M::Pcmpgtb
            | M::Pcmpgtw
            | M::Pcmpgtd
            | M::Pcmpgtq
            | M::Vpcmpeqb
            | M::Vpcmpeqw
            | M::Vpcmpeqd
            | M::Vpcmpeqq
            | M::Vpcmpgtb
            | M::Vpcmpgtw
            | M::Vpcmpgtd
            | M::Vpcmpgtq => self.lane_compare(i, m),
            M::Pminub | M::Pmaxub | M::Vpminub | M::Vpmaxub => self.byte_extreme(i, m),
            M::Pmovmskb
            | M::Vpmovmskb
            | M::Movmskps
            | M::Movmskpd
            | M::Vmovmskps
            | M::Vmovmskpd => self.sign_mask(i, m),
            M::Psrldq | M::Pslldq | M::Vpsrldq | M::Vpslldq => self.byte_shift(i, m),
            M::Psraw | M::Psrad | M::Vpsraw | M::Vpsrad => self.arith_shift(i, m),
            M::Pshuflw | M::Pshufhw | M::Vpshuflw | M::Vpshufhw => self.word_shuffle(i, m),
            M::Pinsrw | M::Vpinsrw => self.insert_word(i),
            M::Pextrb | M::Vpextrb => self.extract_lane(i, 1),
            M::Pextrw | M::Vpextrw => self.extract_lane(i, 2),
            M::Pextrd | M::Vpextrd => self.extract_lane(i, 4),
            M::Pextrq | M::Vpextrq => self.extract_lane(i, 8),
            M::Ptest | M::Vptest => self.packed_test(i),
            M::Vmovaps | M::Vmovups | M::Vmovapd | M::Vmovupd | M::Vmovdqa | M::Vmovdqu => self
                .vector_operand(i, 1)
                .and_then(|v| self.vector_store(i, v)),
            M::Vmovss | M::Vmovsd | M::Vmovd | M::Vmovq => self.vex_scalar_move(i, m),
            _ => return None,
        })
    }

    /// A scalar floating operation: the low lane computed, the rest of the
    /// destination kept (legacy) or taken from the first source (VEX).
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    /// * `width` - The lane.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written, or unmodeled for an operation this does not compute.
    fn scalar_float(&mut self, i: &Instruction, m: Mnemonic, width: Width) -> Result<(), Stop> {
        let rest = self.vector_operand(i, u32::from(i.op_count() >= 3))?;
        let a = lo64(rest & width.lane());
        let b = self.lane_operand(i, i.op_count() - 1, width.bytes())?;
        let r = arith(m, a, b, width).ok_or_else(|| Stop::Unmodeled(format!("{m:?}")))?;
        self.vector_store(i, (rest & !width.lane()) | u128::from(r))
    }

    /// A packed floating operation over every lane.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    /// * `width` - The lanes.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written, or unmodeled for an operation this does not compute.
    fn packed_float(&mut self, i: &Instruction, m: Mnemonic, width: Width) -> Result<(), Stop> {
        if arith(m, 0, 0, width).is_none() {
            return Err(Stop::Unmodeled(format!("{m:?}")));
        }
        let (a, b) = self.sources(i)?;
        let v = packed(a, b, width.bits(), |x, y| {
            arith(m, x, y, width).unwrap_or(0)
        });
        self.vector_store(i, v)
    }

    /// `cmpss` and `cmpsd`: the low lane becomes all ones when the
    /// predicate holds, and zero otherwise.
    ///
    /// The eight SSE predicates are `eq`, `lt`, `le`, `unord`, `neq`,
    /// `nlt`, `nle` and `ord`. A NaN makes the ordered ones false and the
    /// negated ones true, and the two zeros compare equal, as C's
    /// operators do. The bits above the lane stay. A predicate past 7 is
    /// left unmodeled.
    ///
    /// # Arguments
    ///
    /// * `i` - The compare.
    /// * `width` - The lane.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written, or the predicate is past
    /// 7.
    fn scalar_cmp(&mut self, i: &Instruction, width: Width) -> Result<(), Stop> {
        let rest_op = u32::from(i.op_count() >= 4);
        let rest = self.vector_operand(i, rest_op)?;
        let a = lo64(rest & width.lane());
        let b = self.lane_operand(i, i.op_count() - 2, width.bytes())?;
        let (x, y) = (width.to_f64(a), width.to_f64(b));
        let unordered = x.is_nan() || y.is_nan();
        let holds = match i.immediate8() & 0x1f {
            0 => x == y,
            1 => x < y,
            2 => x <= y,
            3 => unordered,
            4 => x != y,
            5 => unordered || x >= y,
            6 => unordered || x > y,
            7 => !unordered,
            _ => return Err(Stop::Unmodeled(format!("{:?}", i.mnemonic()))),
        };
        let mask = if holds { width.lane() } else { 0 };
        self.vector_store(i, (rest & !width.lane()) | mask)
    }

    /// `comisd`, `ucomisd` and their single forms: zero, parity and carry
    /// say equal, unordered and below, the way an unsigned compare's do,
    /// and the rest clear.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `width` - The lane.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn float_compare(&mut self, i: &Instruction, width: Width) -> Result<(), Stop> {
        let a = self.lane_operand(i, 0, width.bytes())?;
        let b = self.lane_operand(i, 1, width.bytes())?;
        let (x, y) = (width.to_f64(a), width.to_f64(b));
        let (zero, parity, carry) = match x.partial_cmp(&y) {
            None => (true, true, true),
            Some(std::cmp::Ordering::Less) => (false, false, true),
            Some(std::cmp::Ordering::Equal) => (true, false, false),
            Some(std::cmp::Ordering::Greater) => (false, false, false),
        };
        self.flags_zero = zero;
        self.flags_parity = parity;
        self.flags_carry = carry;
        self.flags_sign = false;
        self.flags_over = Some(false);
        Ok(())
    }

    /// `cvtsi2sd` and `cvtsi2ss`: a signed integer of the source's width
    /// into the low lane.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn int_to_float(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let src = i.op_count() - 1;
        let bits = match i.op_kind(src) {
            OpKind::Register => reg_bits(i.op_register(src)),
            _ => u32::try_from(i.memory_size().size().max(4) * 8).unwrap_or(64),
        };
        let v = sign_extend(self.operand(i, src)?, bits);
        let width = if matches!(m, Mnemonic::Cvtsi2sd | Mnemonic::Vcvtsi2sd) {
            Width::Double
        } else {
            Width::Single
        };
        let r = match width {
            Width::Double => {
                #[expect(
                    clippy::cast_precision_loss,
                    reason = "cvtsi2sd rounds the integer to the nearest double by design"
                )]
                let r = (v as f64).to_bits();
                r
            }
            Width::Single => {
                #[expect(
                    clippy::cast_precision_loss,
                    reason = "cvtsi2ss rounds the integer to the nearest single by design"
                )]
                let r = u64::from((v as f32).to_bits());
                r
            }
        };
        let rest = self.vector_operand(i, u32::from(i.op_count() >= 3))?;
        self.vector_store(i, (rest & !width.lane()) | u128::from(r))
    }

    /// `cvtsd2si` and its kin: the low lane into a general register.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `width` - The lane.
    /// * `rounding` - How the fraction goes.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn float_to_int(
        &mut self,
        i: &Instruction,
        width: Width,
        rounding: Rounding,
    ) -> Result<(), Stop> {
        let raw = self.lane_operand(i, 1, width.bytes())?;
        let bits = reg_bits(i.op0_register());
        self.store(i, float_to_int(width.to_f64(raw), bits, rounding))
    }

    /// `cvtss2sd` and `cvtsd2ss`: the low lane between widths.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn float_width(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let widen = matches!(m, Mnemonic::Cvtss2sd | Mnemonic::Vcvtss2sd);
        let src = self.lane_operand(i, i.op_count() - 1, if widen { 4 } else { 8 })?;
        let (bytes, r) = if widen {
            (8, f64::from(f32::from_bits(lo32(src))).to_bits())
        } else {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "cvtsd2ss rounds the double to the nearest single by design"
            )]
            let r = u64::from((f64::from_bits(src) as f32).to_bits());
            (4, r)
        };
        let rest = self.vector_operand(i, u32::from(i.op_count() >= 3))?;
        self.vector_store(i, (rest & !lane(bytes)) | u128::from(r))
    }

    /// The packed conversions between 32-bit integers, singles and doubles.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn packed_convert(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let half = matches!(m, Mnemonic::Cvtdq2pd | Mnemonic::Cvtps2pd);
        let src = if half && i.op1_kind() == OpKind::Memory {
            u128::from(self.lane_operand(i, 1, 8)?)
        } else {
            self.vector_operand(i, 1)?
        };
        let dword = |k: u32| lo32(lo64(src >> (32 * k)));
        let qword = |k: u32| lo64(src >> (64 * k));
        let v = match m {
            Mnemonic::Cvtdq2pd => (0..2).fold(0u128, |v, k| {
                v | u128::from(f64::from(dword(k).cast_signed()).to_bits()) << (64 * k)
            }),
            Mnemonic::Cvtdq2ps => (0..4).fold(0u128, |v, k| {
                #[expect(
                    clippy::cast_precision_loss,
                    reason = "cvtdq2ps rounds the integer to the nearest single by design"
                )]
                let single = dword(k).cast_signed() as f32;
                v | u128::from(single.to_bits()) << (32 * k)
            }),
            Mnemonic::Cvttps2dq => (0..4).fold(0u128, |v, k| {
                let x = f64::from(f32::from_bits(dword(k)));
                v | u128::from(float_to_int(x, 32, Rounding::Truncate)) << (32 * k)
            }),
            Mnemonic::Cvtps2pd => (0..2).fold(0u128, |v, k| {
                v | u128::from(f64::from(f32::from_bits(dword(k))).to_bits()) << (64 * k)
            }),
            Mnemonic::Cvtpd2ps => (0..2).fold(0u128, |v, k| {
                #[expect(
                    clippy::cast_possible_truncation,
                    reason = "cvtpd2ps rounds the double to the nearest single by design"
                )]
                let single = f64::from_bits(qword(k)) as f32;
                v | u128::from(single.to_bits()) << (32 * k)
            }),
            _ => (0..2).fold(0u128, |v, k| {
                let x = f64::from_bits(qword(k));
                v | u128::from(float_to_int(x, 32, Rounding::Truncate)) << (32 * k)
            }),
        };
        self.vector_store(i, v)
    }

    /// The bitwise operations on whole registers: float-typed, packed
    /// integer, or VEX.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn logic(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        use Mnemonic as M;
        let (a, b) = self.sources(i)?;
        let v = match m {
            M::Andps | M::Andpd | M::Pand | M::Vandps | M::Vandpd | M::Vpand => a & b,
            M::Andnps | M::Andnpd | M::Pandn | M::Vandnps | M::Vandnpd | M::Vpandn => !a & b,
            M::Orps | M::Orpd | M::Por | M::Vorps | M::Vorpd | M::Vpor => a | b,
            _ => a ^ b,
        };
        self.vector_store(i, v)
    }

    /// `pcmpeq*` and `pcmpgt*`: each lane all ones where the compare holds
    /// (signed, for greater), zero elsewhere.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn lane_compare(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        use Mnemonic as M;
        let (a, b) = self.sources(i)?;
        let bits = lane_bits(m);
        let equal = matches!(
            m,
            M::Pcmpeqb
                | M::Pcmpeqw
                | M::Pcmpeqd
                | M::Pcmpeqq
                | M::Vpcmpeqb
                | M::Vpcmpeqw
                | M::Vpcmpeqd
                | M::Vpcmpeqq
        );
        let v = packed(a, b, bits, |x, y| {
            let holds = if equal {
                x == y
            } else {
                sign_extend(x, bits) > sign_extend(y, bits)
            };
            if holds { u64::MAX } else { 0 }
        });
        self.vector_store(i, v)
    }

    /// `pminub` and `pmaxub`: the unsigned smaller or larger of each byte
    /// pair, how a `strlen` finds a zero in several blocks at once.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn byte_extreme(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let (a, b) = self.sources(i)?;
        let min = matches!(m, Mnemonic::Pminub | Mnemonic::Vpminub);
        let v = packed(a, b, 8, |x, y| if min { x.min(y) } else { x.max(y) });
        self.vector_store(i, v)
    }

    /// `pmovmskb`, `movmskps` and `movmskpd`: the top bit of each lane,
    /// gathered into a general register.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn sign_mask(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let v = self.vector_operand(i, 1)?;
        let bits: u32 = match m {
            Mnemonic::Pmovmskb | Mnemonic::Vpmovmskb => 8,
            Mnemonic::Movmskps | Mnemonic::Vmovmskps => 32,
            _ => 64,
        };
        let r = (0..128 / bits).fold(0u64, |r, k| {
            r | (((v >> (k * bits + bits - 1)) & 1) as u64) << k
        });
        self.store(i, r)
    }

    /// `psrldq` and `pslldq`: the whole register shifted by whole bytes.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn byte_shift(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let src = self.vector_operand(i, u32::from(i.op_count() >= 3))?;
        let count = u32::from(i.immediate8()).min(16) * 8;
        let v = match (count, matches!(m, Mnemonic::Psrldq | Mnemonic::Vpsrldq)) {
            (128, _) => 0,
            (c, true) => src >> c,
            (c, false) => src << c,
        };
        self.vector_store(i, v)
    }

    /// `psraw` and `psrad`: each lane shifted right keeping its sign; a
    /// count past the width fills the lane with the sign.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn arith_shift(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let n = i.op_count() - 1;
        let count = if i.op_kind(n) == OpKind::Immediate8 {
            u64::from(i.immediate8())
        } else {
            lo64(self.vector_operand(i, n)?)
        };
        let src = self.vector_operand(i, u32::from(i.op_count() >= 3))?;
        let bits = lane_bits(m);
        let shift = lo32(count.min(u64::from(bits) - 1));
        let v = packed(src, 0, bits, |x, _| {
            (sign_extend(x, bits) >> shift).cast_unsigned()
        });
        self.vector_store(i, v)
    }

    /// `pshuflw` and `pshufhw`: the four words of one half reordered by an
    /// immediate's four two-bit fields, the other half copied.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn word_shuffle(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let src = self.vector_operand(i, 1)?;
        let order = i.immediate8();
        let high = matches!(m, Mnemonic::Pshufhw | Mnemonic::Vpshufhw);
        let base = if high { 64 } else { 0 };
        let words = lo64(src >> base);
        let mut half = 0u64;
        for k in 0..4 {
            let from = u32::from(order >> (2 * k) & 3);
            half |= (words >> (16 * from) & 0xffff) << (16 * k);
        }
        let keep = src & !(u128::from(u64::MAX) << base);
        self.vector_store(i, keep | u128::from(half) << base)
    }

    /// `pinsrw`: a word from a register or memory into the lane an
    /// immediate names.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn insert_word(&mut self, i: &Instruction) -> Result<(), Stop> {
        let n = i.op_count() - 2;
        let word = u128::from(self.lane_operand(i, n, 2)? & 0xffff);
        let rest = self.vector_operand(i, if i.op_count() >= 4 { 1 } else { 0 })?;
        let at = u32::from(i.immediate8() & 7) * 16;
        self.vector_store(i, (rest & !(0xffff << at)) | word << at)
    }

    /// `pextrb`, `pextrw`, `pextrd`, `pextrq`: the lane an immediate names,
    /// zero-extended into a general register or written to memory.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `bytes` - The lane's width.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn extract_lane(&mut self, i: &Instruction, bytes: usize) -> Result<(), Stop> {
        let src = self.vector_operand(i, 1)?;
        let lanes = 16 / bytes;
        let at = (usize::from(i.immediate8()) % lanes) * bytes * 8;
        let mask = if bytes == 8 {
            u128::from(u64::MAX)
        } else {
            (1u128 << (bytes * 8)) - 1
        };
        let v = lo64((src >> at) & mask);
        if i.op0_kind() == OpKind::Register && i.op0_register().is_gpr() {
            self.store(i, v)
        } else {
            let addr = self.mem_addr(i)?;
            self.write(addr, v, bytes)
        }
    }

    /// `ptest a, b`: ZF when `a & b` is zero, CF when `~a & b` is; the
    /// other flags clear.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read.
    fn packed_test(&mut self, i: &Instruction) -> Result<(), Stop> {
        let a = self.vector_operand(i, 0)?;
        let b = self.vector_operand(i, 1)?;
        self.flags_zero = a & b == 0;
        self.flags_carry = !a & b == 0;
        self.flags_sign = false;
        self.flags_parity = false;
        self.flags_over = Some(false);
        Ok(())
    }

    /// `vmovss`, `vmovsd`, `vmovd` and `vmovq`: a load zeroes the rest of
    /// the register, a store writes the lane, and the three-register
    /// `vmovss`/`vmovsd` merge the second source's lane into the first's.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    fn vex_scalar_move(&mut self, i: &Instruction, m: Mnemonic) -> Result<(), Stop> {
        let width = Width::of_scalar(m);
        let bytes = width.bytes();
        if i.op_count() == 3 {
            let rest = self.vector_operand(i, 1)?;
            let low = self.vector_operand(i, 2)? & width.lane();
            return self.vector_store(i, (rest & !width.lane()) | low);
        }
        if i.op0_kind() == OpKind::Register && xmm_slot(i.op0_register()).is_some() {
            let v = self.lane_operand(i, 1, bytes)?;
            return self.vector_store(i, u128::from(v));
        }
        let v = self.lane_operand(i, 1, bytes)?;
        if i.op0_kind() == OpKind::Memory {
            let addr = self.mem_addr(i)?;
            self.write(addr, v, bytes)
        } else {
            self.store(i, v)
        }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::super::tests::{image, returned};

    /// Scalar doubles divide, convert back truncated and rounded to even,
    /// and compare with the flags an unsigned compare would set; a NaN
    /// compares unordered.
    #[test]
    fn scalar_doubles_compute_convert_and_compare() {
        let emu = returned(image(
            &[
                0xb8, 0x07, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x2a, 0xc0, 0xb8, 0x02, 0x00, 0x00, 0x00,
                0xf2, 0x0f, 0x2a, 0xc8, 0xf2, 0x0f, 0x5e, 0xc1, 0xf2, 0x0f, 0x2c, 0xc8, 0xf2, 0x0f,
                0x2d, 0xd0, 0x66, 0x0f, 0x2e, 0xc1, 0x41, 0x0f, 0x97, 0xc0, 0xf2, 0x0f, 0x51, 0xd1,
                0x66, 0x0f, 0x2f, 0xd1, 0x41, 0x0f, 0x92, 0xc1, 0x0f, 0x57, 0xdb, 0xf2, 0x0f, 0x5e,
                0xdb, 0x66, 0x0f, 0x2e, 0xdb, 0x41, 0x0f, 0x9a, 0xc2, 0x66, 0x48, 0x0f, 0x7e, 0xc0,
                0xc3,
            ],
            &[],
        ));
        assert_eq!(emu.register("rax"), Some(3.5f64.to_bits()), "7 / 2");
        assert_eq!(emu.register("rcx"), Some(3), "truncated");
        assert_eq!(emu.register("rdx"), Some(4), "3.5 rounds to even");
        assert_eq!(emu.register("r8"), Some(1), "3.5 is above 2");
        assert_eq!(emu.register("r9"), Some(1), "the root of 2 is below 2");
        assert_eq!(emu.register("r10"), Some(1), "0 / 0 compares unordered");
    }

    /// `ptest` sets ZF when the operands share no bits and CF when the
    /// second's bits all lie in the first's, and the lane extracts of every
    /// width read the lane the immediate names, into a register or memory.
    #[test]
    fn packed_tests_and_lane_extracts() {
        let mut data = vec![0u8; 32];
        for (k, b) in (0u8..).zip(data.iter_mut().take(16)) {
            *b = k;
        }
        let emu = returned(image(
            &[
                0xf3, 0x0f, 0x6f, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0x66, 0x0f, 0xef, 0xc9, 0x66,
                0x0f, 0x38, 0x17, 0xc1, 0x0f, 0x94, 0xc0, 0x0f, 0x92, 0xc1, 0x66, 0x0f, 0x38, 0x17,
                0xc0, 0x0f, 0x94, 0xc2, 0x66, 0x0f, 0x3a, 0x16, 0xc6, 0x01, 0x66, 0x48, 0x0f, 0x3a,
                0x16, 0xc7, 0x01, 0x66, 0x41, 0x0f, 0x3a, 0x14, 0xc0, 0x03, 0x66, 0x0f, 0x3a, 0x16,
                0x04, 0x25, 0x10, 0x20, 0x00, 0x00, 0x02, 0x44, 0x8b, 0x0c, 0x25, 0x10, 0x20, 0x00,
                0x00, 0xc3,
            ],
            &data,
        ));
        assert_eq!(emu.register("rax"), Some(1), "no bit in common with zero");
        assert_eq!(emu.register("rcx"), Some(1), "zero's bits all lie in it");
        assert_eq!(emu.register("rdx"), Some(0), "it shares its own bits");
        assert_eq!(emu.register("rsi"), Some(0x0706_0504), "dword 1");
        assert_eq!(emu.register("rdi"), Some(0x0f0e_0d0c_0b0a_0908), "qword 1");
        assert_eq!(emu.register("r8"), Some(3), "byte 3");
        assert_eq!(
            emu.register("r9"),
            Some(0x0b0a_0908),
            "dword 2, through memory"
        );
    }

    /// A vectorized `strlen` step finds the terminator, and byte shifts,
    /// word shuffles and word extracts move the lanes they name.
    #[test]
    fn packed_bytes_find_a_terminator_and_move() {
        let emu = returned(image(
            &[
                0x66, 0x0f, 0xef, 0xc0, 0xf3, 0x0f, 0x6f, 0x0c, 0x25, 0x00, 0x20, 0x00, 0x00, 0x66,
                0x0f, 0x74, 0xc8, 0x66, 0x0f, 0xd7, 0xc1, 0x0f, 0xbc, 0xc0, 0xf3, 0x0f, 0x6f, 0x14,
                0x25, 0x00, 0x20, 0x00, 0x00, 0x66, 0x0f, 0x73, 0xda, 0x02, 0x66, 0x0f, 0x7e, 0xd1,
                0xf2, 0x0f, 0x70, 0xda, 0x1b, 0x66, 0x48, 0x0f, 0x7e, 0xda, 0x66, 0x44, 0x0f, 0xc5,
                0xc2, 0x01, 0xc3,
            ],
            b"hello\0",
        ));
        assert_eq!(emu.register("rax"), Some(5), "the terminator is byte 5");
        assert_eq!(emu.register("rcx"), Some(0x006f_6c6c), "\"llo\0\"");
        assert_eq!(
            emu.register("rdx"),
            Some(0x6c6c_006f_0000_0000),
            "words reversed"
        );
        assert_eq!(emu.register("r8"), Some(0x6f), "word 1 is \"o\0\"");
    }

    /// The VEX forms take their two sources apart from the destination.
    #[test]
    fn vex_forms_read_two_sources() {
        let emu = returned(image(
            &[
                0xc5, 0xf8, 0x57, 0xc0, 0xb8, 0x03, 0x00, 0x00, 0x00, 0xc5, 0xfb, 0x2a, 0xc8, 0xc5,
                0xf3, 0x58, 0xd1, 0xc5, 0xfb, 0x2c, 0xc2, 0xc5, 0xf8, 0x77, 0xc3,
            ],
            &[],
        ));
        assert_eq!(emu.register("rax"), Some(6));
    }

    /// The 256-bit forms whose halves compute independently run instead of
    /// stopping the run.
    ///
    /// A ymm load fills the low lane, `vpaddb` adds each byte of it, a
    /// register-to-register move carries both halves along, `vpaddq` doubles
    /// the low lane's qwords, and a store writes the low lane's sixteen
    /// bytes (the width the decompiler models a ymm access at); a
    /// cross-lane instruction stays unmodeled.
    ///
    /// # Panics
    ///
    /// When a lane reads wrong, or the cross-lane form runs.
    #[test]
    fn ymm_lane_pairs_compute_and_move_instead_of_stopping() {
        let mut data: Vec<u8> = Vec::new();
        data.extend((0u8..32).collect::<Vec<u8>>());
        let emu = returned(image(
            &[
                0xc5, 0xfd, 0x6f, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xc5, 0xfe, 0x6f, 0x0c, 0x25,
                0x10, 0x20, 0x00, 0x00, 0xc5, 0xed, 0xef, 0xd2, 0xc5, 0xfd, 0xfc, 0xd1, 0xc5, 0xfe,
                0x7f, 0x14, 0x25, 0x00, 0x21, 0x00, 0x00, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x21, 0x00,
                0x00, 0x48, 0x8b, 0x0c, 0x25, 0x08, 0x21, 0x00, 0x00, 0xc5, 0xfd, 0x6f, 0xda, 0xc5,
                0xe5, 0xd4, 0xe3, 0xc5, 0xfe, 0x7f, 0x24, 0x25, 0x40, 0x21, 0x00, 0x00, 0x48, 0x8b,
                0x14, 0x25, 0x40, 0x21, 0x00, 0x00, 0xc3,
            ],
            &data,
        ));
        assert_eq!(
            emu.register("rax"),
            Some(0x1e1c_1a18_1614_1210),
            "each low-lane byte k met byte 16+k"
        );
        assert_eq!(
            emu.register("rcx"),
            Some(0x2e2c_2a28_2624_2220),
            "the high qwords of the same lane"
        );
        assert_eq!(
            emu.register("rdx"),
            Some(0x3c38_3430_2c28_2420),
            "the doubled qword lane came through the register move"
        );

        // ASM: vmovdqa ymm0,[0x2000]; vinsertf128 ymm4,ymm4,xmm0,1; ret
        let p = image(
            &[
                0xc5, 0xfd, 0x6f, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xc4, 0xe3, 0x5d, 0x18, 0xe0,
                0x01, 0xc3,
            ],
            &data,
        );
        let mut emu = super::Emulator::new(&p, 100).expect("emulator");
        let run = emu.run(0x1000);
        assert!(
            matches!(&run.stop, super::Stop::Unmodeled(what) if what == "Vinsertf128"),
            "{:?}",
            run.stop
        );
    }
}
