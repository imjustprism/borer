//! Integer arithmetic, logic and shifts, with the flags each sets.

use super::{Emulator, Stop, lo64, mask, op_bits, rotate_left, rotate_right, sign_extend};
use crate::isa::x86::{Instruction, Mnemonic};
use crate::num::lo32;

/// An arithmetic or logic instruction: what it computes from operand 0 and
/// its source, and the flags it leaves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Alu {
    /// `add`.
    Add,
    /// `adc`: an add with the carry in.
    Adc,
    /// `sub`.
    Sub,
    /// `sbb`: a subtract with the carry in.
    Sbb,
    /// `xor`.
    Xor,
    /// `and`.
    And,
    /// `or`.
    Or,
    /// `cmp`: a subtract that writes only the flags.
    Cmp,
    /// `test`: an and that writes only the flags.
    Test,
}

impl Alu {
    /// The operation a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The operation, or `None` when `m` is not one of these.
    pub(super) fn of(m: Mnemonic) -> Option<Alu> {
        Some(match m {
            Mnemonic::Add => Alu::Add,
            Mnemonic::Adc => Alu::Adc,
            Mnemonic::Sub => Alu::Sub,
            Mnemonic::Sbb => Alu::Sbb,
            Mnemonic::Xor => Alu::Xor,
            Mnemonic::And => Alu::And,
            Mnemonic::Or => Alu::Or,
            Mnemonic::Cmp => Alu::Cmp,
            Mnemonic::Test => Alu::Test,
            _ => return None,
        })
    }
}

/// A shift or rotate of operand 0 by a count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Shift {
    /// `shl`: left, zeros in.
    Shl,
    /// `shr`: right, zeros in.
    Shr,
    /// `sar`: right, the sign in.
    Sar,
    /// `rol`: a rotate left.
    Rol,
    /// `ror`: a rotate right.
    Ror,
    /// `rcl`: a rotate left through the carry.
    Rcl,
    /// `rcr`: a rotate right through the carry.
    Rcr,
}

impl Shift {
    /// The shift a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The shift, or `None` when `m` is not one of these.
    pub(super) fn of(m: Mnemonic) -> Option<Shift> {
        Some(match m {
            Mnemonic::Shl => Shift::Shl,
            Mnemonic::Shr => Shift::Shr,
            Mnemonic::Sar => Shift::Sar,
            Mnemonic::Rol => Shift::Rol,
            Mnemonic::Ror => Shift::Ror,
            Mnemonic::Rcl => Shift::Rcl,
            Mnemonic::Rcr => Shift::Rcr,
            _ => return None,
        })
    }
}

impl Emulator<'_> {
    /// An arithmetic or logic instruction that writes operand 0 and flags.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - What it computes.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    pub(super) fn alu(&mut self, i: &Instruction, op: Alu) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        let a = u128::from(mask(self.dest(i)?, bits));
        let b = u128::from(mask(self.source(i)?, bits));
        let cin = u128::from(self.flags_carry);
        let top = 1u128 << bits;
        let (r, carry) = match op {
            Alu::Add => {
                let s = a + b;
                (lo64(s), s >= top)
            }
            Alu::Adc => {
                let s = a + b + cin;
                (lo64(s), s >= top)
            }
            Alu::Sub | Alu::Cmp => (lo64(a.wrapping_sub(b)), a < b),
            Alu::Sbb => (lo64(a.wrapping_sub(b).wrapping_sub(cin)), a < b + cin),
            Alu::Xor => (lo64(a ^ b), false),
            Alu::And | Alu::Test => (lo64(a & b), false),
            Alu::Or => (lo64(a | b), false),
        };
        let r = mask(r, bits);
        self.flags_carry = carry;
        self.set_flags(r, bits);
        let signed = |v: u128| v >> (bits - 1) & 1 == 1;
        self.flags_over = Some(match op {
            Alu::Add | Alu::Adc => signed(a) == signed(b) && signed(u128::from(r)) != signed(a),
            Alu::Sub | Alu::Cmp | Alu::Sbb => {
                signed(a) != signed(b) && signed(u128::from(r)) != signed(a)
            }
            Alu::Xor | Alu::And | Alu::Or | Alu::Test => false,
        });
        if !matches!(op, Alu::Cmp | Alu::Test) {
            self.store(i, r)?;
        }
        Ok(None)
    }

    /// `inc`, `dec`, `neg` and `not` on operand 0, with the flags each sets.
    ///
    /// `inc` and `dec` leave carry as it was and set overflow when the
    /// operand steps into or out of the signed minimum (`0x7fff.. + 1` or
    /// `0x8000.. - 1`); `neg` is `0 - a` and sets carry for any non-zero
    /// operand; `not` touches no flags.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    ///
    /// # Errors
    ///
    /// When operand 0 cannot be read or written.
    pub(super) fn unary(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        let a = mask(self.dest(i)?, bits);
        let half = 1u64 << (bits - 1);
        let r = match m {
            Mnemonic::Inc => {
                let r = mask(a.wrapping_add(1), bits);
                self.set_flags(r, bits);
                self.flags_over = Some(r == half);
                r
            }
            Mnemonic::Dec => {
                let r = mask(a.wrapping_sub(1), bits);
                self.set_flags(r, bits);
                self.flags_over = Some(a == half);
                r
            }
            Mnemonic::Neg => {
                let r = mask(0u64.wrapping_sub(a), bits);
                self.flags_carry = a != 0;
                self.set_flags(r, bits);
                self.flags_over = Some(a == half);
                r
            }
            _ => !a,
        };
        self.store(i, r)?;
        Ok(None)
    }

    /// A shift or rotate of operand 0 by operand 1.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `op` - Which shift.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    pub(super) fn shift(&mut self, i: &Instruction, op: Shift) -> Result<Option<u64>, Stop> {
        let a = self.dest(i)?;
        let bits = op_bits(i);
        let modulo = if bits == 64 { 0x3f } else { 0x1f };
        let count = lo32(self.source(i)? & modulo);
        if count == 0 {
            self.store(i, mask(a, bits))?;
            return Ok(None);
        }
        let v = mask(a, bits);
        let top = bits.saturating_sub(1);
        let (r, carry) = match op {
            Shift::Shl => (
                v.wrapping_shl(count),
                count <= bits && (v >> (bits - count)) & 1 == 1,
            ),
            Shift::Shr => (v.wrapping_shr(count), (v >> (count - 1).min(63)) & 1 == 1),
            Shift::Sar => (
                (sign_extend(a, bits) >> count.min(63)).cast_unsigned(),
                (sign_extend(a, bits) >> (count - 1).min(63)) & 1 == 1,
            ),
            Shift::Rol => {
                let r = rotate_left(v, count, bits);
                (r, r & 1 == 1)
            }
            Shift::Ror => {
                let r = rotate_right(v, count, bits);
                (r, (r >> top) & 1 == 1)
            }
            Shift::Rcl | Shift::Rcr => {
                let width = bits + 1;
                let n = count % width;
                let wide = (u128::from(self.flags_carry) << bits) | u128::from(v);
                let rotated = if op == Shift::Rcl {
                    (wide << n) | (wide >> (width - n))
                } else {
                    (wide >> n) | (wide << (width - n))
                };
                let out = (rotated >> bits) & 1 == 1;
                (mask(lo64(rotated), bits), out)
            }
        };
        let r = mask(r, bits);
        self.flags_carry = carry;
        self.set_flags(r, bits);
        let msb = |x: u64| x >> top & 1 == 1;
        self.flags_over = (count == 1).then(|| match op {
            Shift::Shl | Shift::Rol | Shift::Rcl => msb(r) != carry,
            Shift::Shr => msb(v) != msb(r),
            Shift::Sar => false,
            Shift::Ror | Shift::Rcr => msb(r) != (r >> (top - 1) & 1 == 1),
        });
        self.store(i, r)?;
        Ok(None)
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::super::tests::{image, returned};

    /// `inc` and `dec` set the overflow flag and preserve carry, so signed
    /// conditions (`setg`, `setl`, `seto`) after them read a defined flag.
    #[test]
    fn inc_and_dec_set_overflow_and_preserve_carry() {
        let emu = returned(image(
            &[
                0xf9, // ASM: stc
                0xb8, 0xff, 0xff, 0xff, 0x7f, // ASM: mov eax,0x7fffffff
                0xff, 0xc0, // ASM: inc eax
                0x0f, 0x90, 0xc1, // ASM: seto cl
                0x0f, 0x92, 0xc2, // ASM: setb dl
                0xff, 0xc8, // ASM: dec eax
                0x41, 0x0f, 0x90, 0xc0, // ASM: seto r8b
                0x41, 0x0f, 0x9c, 0xc1, // ASM: setl r9b
                0xff, 0xc8, // ASM: dec eax
                0x41, 0x0f, 0x9f, 0xc2, // ASM: setg r10b
                0xc3, // ASM: ret
            ],
            &[],
        ));
        assert_eq!(emu.register("rax"), Some(0x7fff_fffe));
        assert_eq!(emu.register("rcx"), Some(1), "0x7fffffff + 1 overflows");
        assert_eq!(emu.register("rdx"), Some(1), "inc preserves carry");
        assert_eq!(emu.register("r8"), Some(1), "0x80000000 - 1 overflows");
        assert_eq!(emu.register("r9"), Some(1), "SF != OF on signed underflow");
        assert_eq!(emu.register("r10"), Some(1), "0x7ffffffe > 0 signed");
    }
}
