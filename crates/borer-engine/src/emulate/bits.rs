//! Bit-level integer instructions: one-bit tests and updates, scans and
//! counts, byte swaps, double-width shifts, and widening multiplies.
//!
//! These are the integer instructions a real binary uses that the core
//! arithmetic does not cover. Measured over five system binaries, a bit
//! test was the most common instruction the emulator stopped on: a flag
//! word is read with `bt`, a lock is taken with `lock bts`, and a string
//! routine finds its terminator with `bsf` or `tzcnt`.

use super::{Emulator, Stop, lo64, mask, op_bits, operand_bytes, remainder, sign_extend, sized_ax};
use crate::isa::x86::{Instruction, Mnemonic, OpKind, Register};
use crate::num::lo32;

impl Emulator<'_> {
    /// `bt`, `bts`, `btr` and `btc`: copies one bit of operand 0 into the
    /// carry flag, then leaves it, sets it, clears it or flips it.
    ///
    /// A register offset into memory addresses a bit string rather than the
    /// operand alone: its high bits, signed, move the address by whole
    /// operands, so `bt dword [rcx], eax` with `eax` 100 tests bit 4 of the
    /// fourth dword past `rcx`. An immediate offset, or any offset into a
    /// register, is taken modulo the width. Only the carry is defined after;
    /// the overflow goes unknown and the zero flag is kept.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    pub(super) fn bit_test(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        let offset = self.operand(i, 1)?;
        let (at, bit) = if i.op0_kind() == OpKind::Memory && i.op1_kind() == OpKind::Register {
            // SPEC: Intel SDM Vol. 2A, BT: a register BitOffset into memory ranges over -2^31..2^31-1 (or the operand's width), addressing a bit string.
            let signed = sign_extend(offset, bits);
            let width = i64::from(bits);
            let base = self.mem_addr(i)?;
            let moved = base.wrapping_add_signed(signed.div_euclid(width) * (width / 8));
            (
                Some(self.narrow(moved)),
                lo32(signed.rem_euclid(width).cast_unsigned()),
            )
        } else {
            (None, lo32(offset % u64::from(bits)))
        };
        let bytes = (bits / 8) as usize;
        let v = match at {
            Some(a) => self.load(a, bytes)?,
            None => self.operand(i, 0)?,
        };
        self.flags_carry = v >> bit & 1 == 1;
        self.flags_over = None;
        let r = match m {
            Mnemonic::Bts => v | 1 << bit,
            Mnemonic::Btr => v & !(1 << bit),
            Mnemonic::Btc => v ^ 1 << bit,
            _ => return Ok(None),
        };
        match at {
            Some(a) => self.write(a, r, bytes)?,
            None => self.store(i, r)?,
        }
        Ok(None)
    }

    /// `bsf`, `bsr`, `tzcnt`, `lzcnt` and `popcnt`.
    ///
    /// A scan of zero sets the zero flag and leaves its destination as it
    /// was, which is what the hardware does though only AMD documents it;
    /// the counts define zero as the width. `tzcnt` and `lzcnt` are taken
    /// as themselves, not as the `bsf` and `bsr` an older CPU decodes them
    /// as.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `m` - Its mnemonic.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    pub(super) fn bit_count(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        let v = mask(self.operand(i, 1)?, bits);
        self.flags_over = None;
        let r = match m {
            Mnemonic::Bsf | Mnemonic::Bsr => {
                self.flags_zero = v == 0;
                if v == 0 {
                    return Ok(None);
                }
                if m == Mnemonic::Bsf {
                    v.trailing_zeros()
                } else {
                    63 - v.leading_zeros()
                }
            }
            Mnemonic::Tzcnt | Mnemonic::Lzcnt => {
                let r = if m == Mnemonic::Tzcnt {
                    v.trailing_zeros().min(bits)
                } else {
                    v.leading_zeros() - (64 - bits)
                };
                self.flags_carry = v == 0;
                self.flags_zero = r == 0;
                r
            }
            _ => {
                // SPEC: Intel SDM Vol. 2B, POPCNT: ZF is set for a zero source; OF, SF, AF, CF and PF are cleared.
                self.flags_zero = v == 0;
                self.flags_carry = false;
                self.flags_sign = false;
                self.flags_parity = false;
                self.flags_over = Some(false);
                v.count_ones()
            }
        };
        self.store(i, u64::from(r))?;
        Ok(None)
    }

    /// `bswap`: reverses the bytes of a 32- or 64-bit register, the step
    /// that reads a big-endian length or checksum.
    ///
    /// # Errors
    ///
    /// Unmodeled for the 16-bit form, whose result the manual leaves
    /// undefined.
    pub(super) fn byte_swap(&mut self, i: &Instruction) -> Result<Option<u64>, Stop> {
        let v = self.operand(i, 0)?;
        let r = match op_bits(i) {
            64 => v.swap_bytes(),
            32 => u64::from(lo32(v).swap_bytes()),
            _ => return Err(Stop::Unmodeled("16-bit Bswap".to_owned())),
        };
        self.store(i, r)?;
        Ok(None)
    }

    /// `shld` and `shrd`: shifts operand 0, filling the vacated bits from
    /// operand 1, by an immediate or `cl`. A compiler builds a 128-bit shift
    /// from these, and a 32-bit target every 64-bit one.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written, or unmodeled for a 16-bit
    /// count past the width, whose result the manual leaves undefined.
    pub(super) fn double_shift(
        &mut self,
        i: &Instruction,
        m: Mnemonic,
    ) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        let a = mask(self.operand(i, 0)?, bits);
        let b = mask(self.operand(i, 1)?, bits);
        let modulo = if bits == 64 { 0x3f } else { 0x1f };
        let count = lo32(self.operand(i, 2)? & modulo);
        // A shift by zero leaves every flag alone, as for a plain shift.
        if count == 0 {
            self.store(i, a)?;
            return Ok(None);
        }
        if count > bits {
            return Err(Stop::Unmodeled(format!("{m:?} past the width")));
        }
        let (r, carry) = if m == Mnemonic::Shld {
            let wide = (u128::from(a) << bits | u128::from(b)) << count;
            (lo64(wide >> bits), a >> (bits - count) & 1 == 1)
        } else {
            let wide = (u128::from(b) << bits | u128::from(a)) >> count;
            (lo64(wide), a >> (count - 1) & 1 == 1)
        };
        let r = mask(r, bits);
        self.flags_carry = carry;
        self.set_flags(r, bits);
        self.store(i, r)?;
        Ok(None)
    }

    /// The BMI shifts and `andn`: `shlx`, `shrx` and `sarx` shift by a
    /// register taken modulo the width and leave the flags alone, `rorx`
    /// rotates by an immediate, and `andn` ands the complement of its first
    /// source and sets the flags of the result.
    ///
    /// # Errors
    ///
    /// When an operand cannot be read or written.
    pub(super) fn bmi(&mut self, i: &Instruction, m: Mnemonic) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        let a = mask(self.operand(i, 1)?, bits);
        let b = self.operand(i, 2)?;
        let count = lo32(b & u64::from(bits - 1));
        let r = match m {
            Mnemonic::Shlx => a << count,
            Mnemonic::Shrx => a >> count,
            Mnemonic::Sarx => (sign_extend(a, bits) >> count).cast_unsigned(),
            Mnemonic::Rorx => {
                if count == 0 {
                    a
                } else {
                    a >> count | a << (bits - count)
                }
            }
            _ => {
                let r = mask(!a & b, bits);
                self.flags_carry = false;
                self.set_flags(r, bits);
                self.flags_over = Some(false);
                r
            }
        };
        self.store(i, mask(r, bits))?;
        Ok(None)
    }

    /// The one-operand `mul` and `imul`: the accumulator times operand 0,
    /// the double-width product in `ah:al`, `dx:ax`, `edx:eax` or
    /// `rdx:rax`. A compiler divides by a constant with the high half of
    /// one, and a hash mixes with the whole product.
    ///
    /// Carry and overflow say the product needs its high half: any bit of
    /// it for `mul`, anything but the low half's sign for `imul`.
    ///
    /// # Errors
    ///
    /// When the operand cannot be read.
    pub(super) fn widening_multiply(
        &mut self,
        i: &Instruction,
        m: Mnemonic,
    ) -> Result<Option<u64>, Stop> {
        let w = operand_bytes(i, 0);
        let bits = op_bits(i);
        let src = self.operand(i, 0)?;
        let acc = self.reg_sized(sized_ax(w));
        let (lo, hi, wide) = if m == Mnemonic::Mul {
            let p = u128::from(mask(acc, bits)) * u128::from(mask(src, bits));
            let hi = mask(lo64(p >> bits), bits);
            (mask(lo64(p), bits), hi, hi != 0)
        } else {
            let p = i128::from(sign_extend(acc, bits)) * i128::from(sign_extend(src, bits));
            let lo = mask(lo64(p.cast_unsigned()), bits);
            (
                lo,
                mask(lo64((p >> bits).cast_unsigned()), bits),
                p != i128::from(sign_extend(lo, bits)),
            )
        };
        if w == 1 {
            self.set_reg_sized(Register::AX, hi << 8 | lo);
        } else {
            self.set_reg_sized(sized_ax(w), lo);
            self.set_reg_sized(remainder(w), hi);
        }
        self.flags_carry = wide;
        self.set_flags(lo, bits);
        self.flags_over = Some(wide);
        Ok(None)
    }

    /// The two- and three-operand `imul`: a product truncated to operand 0's
    /// width, with carry and overflow set when the truncation lost anything.
    ///
    /// Rust checks every multiply for overflow this way (`imul` then `jo` or
    /// `seto`), so a product that left the flags as they were took whichever
    /// branch the instruction before had chosen.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    /// * `a` - The multiplicand.
    /// * `b` - The multiplier.
    ///
    /// # Errors
    ///
    /// When the destination cannot be written.
    pub(super) fn truncating_multiply(
        &mut self,
        i: &Instruction,
        a: u64,
        b: u64,
    ) -> Result<Option<u64>, Stop> {
        let bits = op_bits(i);
        let p = i128::from(sign_extend(a, bits)) * i128::from(sign_extend(b, bits));
        let r = mask(lo64(p.cast_unsigned()), bits);
        let lost = p != i128::from(sign_extend(r, bits));
        self.flags_carry = lost;
        self.set_flags(r, bits);
        self.flags_over = Some(lost);
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

    /// A bit test copies the bit into the carry; a register offset into
    /// memory walks a bit string, whole dwords at a time and backward for a
    /// negative offset.
    #[test]
    fn bit_tests_read_and_write_a_bit_string() {
        let emu = returned(image(
            &[
                0xb8, 0x10, 0x00, 0x00, 0x00, // mov eax,0x10
                0x0f, 0xba, 0xe0, 0x04, // bt eax,4
                0x0f, 0x92, 0xc1, // setc cl
                0xbe, 0x00, 0x20, 0x00, 0x00, // mov esi,0x2000
                0xba, 0x64, 0x00, 0x00, 0x00, // mov edx,100
                0x0f, 0xab, 0x16, // bts [rsi],edx
                0xba, 0xff, 0xff, 0xff, 0xff, // mov edx,-1
                0x0f, 0xab, 0x56, 0x10, // bts [rsi+0x10],edx
                0x44, 0x8b, 0x46, 0x0c, // mov r8d,[rsi+0xc]
                0x0f, 0xba, 0xf8, 0x04, // btc eax,4
                0x0f, 0x92, 0xc3, // setc bl
                0xc3, // ret
            ],
            &[],
        ));
        assert_eq!(emu.register("rcx"), Some(1), "bit 4 of 0x10 is set");
        assert_eq!(
            emu.register("r8"),
            Some(0x8000_0010),
            "bit 100 is bit 4 of the fourth dword; bit -1 is bit 31 of the one before 0x2010"
        );
        assert_eq!(emu.register("rax"), Some(0), "btc cleared the bit");
        assert_eq!(emu.register("rbx"), Some(1), "btc reported it was set");
    }

    /// `mul` and one-operand `imul` fill the high half and say whether it
    /// was needed; a truncating `imul` says whether it lost bits.
    #[test]
    fn multiplies_widen_or_report_what_they_lost() {
        let emu = returned(image(
            &[
                0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff, // mov rax,-1
                0x48, 0xc7, 0xc1, 0x02, 0x00, 0x00, 0x00, // mov rcx,2
                0x48, 0xf7, 0xe1, // mul rcx
                0x0f, 0x92, 0xc3, // setc bl
                0x49, 0x89, 0xc0, // mov r8,rax
                0x49, 0x89, 0xd1, // mov r9,rdx
                0xb8, 0xfd, 0xff, 0xff, 0xff, // mov eax,-3
                0xb9, 0x05, 0x00, 0x00, 0x00, // mov ecx,5
                0xf7, 0xe9, // imul ecx
                0x41, 0x0f, 0x90, 0xc2, // seto r10b
                0xb8, 0x00, 0x00, 0x00, 0x40, // mov eax,0x40000000
                0x6b, 0xc0, 0x04, // imul eax,eax,4
                0x41, 0x0f, 0x90, 0xc3, // seto r11b
                0xb0, 0xc8, // mov al,200
                0xb1, 0x03, // mov cl,3
                0xf6, 0xe1, // mul cl
                0xc3, // ret
            ],
            &[],
        ));
        assert_eq!(emu.register("r8"), Some(0xffff_ffff_ffff_fffe));
        assert_eq!(emu.register("r9"), Some(1));
        assert_eq!(emu.register("rbx"), Some(1), "the high half was needed");
        assert_eq!(
            emu.register("rdx"),
            Some(0xffff_ffff),
            "-15 spread into edx"
        );
        assert_eq!(emu.register("r10"), Some(0), "-15 fits eax");
        assert_eq!(emu.register("r11"), Some(1), "2^32 does not fit eax");
        assert_eq!(emu.register("rax"), Some(0x258), "200 * 3 fills ax");
    }

    /// Scans find the lowest and highest set bit, the counts count, and a
    /// scan of zero leaves its destination and sets the zero flag.
    #[test]
    fn scans_and_counts_find_the_bits() {
        let emu = returned(image(
            &[
                0xb8, 0xf0, 0x00, 0x00, 0x00, // mov eax,0xf0
                0x0f, 0xbc, 0xc8, // bsf ecx,eax
                0x0f, 0xbd, 0xd0, // bsr edx,eax
                0xf3, 0x44, 0x0f, 0xbc, 0xc0, // tzcnt r8d,eax
                0xf3, 0x44, 0x0f, 0xbd, 0xc8, // lzcnt r9d,eax
                0xf3, 0x44, 0x0f, 0xb8, 0xd0, // popcnt r10d,eax
                0x31, 0xf6, // xor esi,esi
                0xbf, 0x07, 0x00, 0x00, 0x00, // mov edi,7
                0x0f, 0xbc, 0xfe, // bsf edi,esi
                0x41, 0x0f, 0x94, 0xc3, // setz r11b
                0xf3, 0x44, 0x0f, 0xbc, 0xe6, // tzcnt r12d,esi
                0xc3, // ret
            ],
            &[],
        ));
        assert_eq!(emu.register("rcx"), Some(4));
        assert_eq!(emu.register("rdx"), Some(7));
        assert_eq!(emu.register("r8"), Some(4));
        assert_eq!(emu.register("r9"), Some(24));
        assert_eq!(emu.register("r10"), Some(4));
        assert_eq!(
            emu.register("rdi"),
            Some(7),
            "a scan of zero writes nothing"
        );
        assert_eq!(emu.register("r11"), Some(1));
        assert_eq!(emu.register("r12"), Some(32), "tzcnt of zero is the width");
    }

    /// The BMI shifts take their count modulo the width from a register.
    #[test]
    fn bmi_shifts_count_modulo_the_width() {
        let emu = returned(image(
            &[
                0xb8, 0x01, 0x00, 0x00, 0x00, // mov eax,1
                0xb9, 0x21, 0x00, 0x00, 0x00, // mov ecx,33
                0xc4, 0xe2, 0x71, 0xf7, 0xd0, // shlx edx,eax,ecx
                0xc3, // ret
            ],
            &[],
        ));
        assert_eq!(emu.register("rdx"), Some(2), "33 is 1 modulo 32");
    }

    /// Byte swaps, double-width shifts, and the flags `lahf`, `setp` and
    /// `cmc` read and write.
    #[test]
    fn swaps_double_shifts_and_flag_moves() {
        let emu = returned(image(
            &[
                0xbb, 0x44, 0x33, 0x22, 0x11, // mov ebx,0x11223344
                0x0f, 0xcb, // bswap ebx
                0x48, 0xb9, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,
                0x01, // mov rcx,0x0102030405060708
                0x48, 0x0f, 0xc9, // bswap rcx
                0xb8, 0x01, 0x00, 0x00, 0x80, // mov eax,0x80000001
                0xba, 0x00, 0x00, 0x00, 0xf0, // mov edx,0xf0000000
                0x0f, 0xa4, 0xd0, 0x04, // shld eax,edx,4
                0xbe, 0xf1, 0x00, 0x00, 0x00, // mov esi,0xf1
                0xbf, 0x0a, 0x00, 0x00, 0x00, // mov edi,0xa
                0x0f, 0xac, 0xfe, 0x04, // shrd esi,edi,4
                0x41, 0x0f, 0x92, 0xc0, // setc r8b
                0x41, 0xb9, 0x03, 0x00, 0x00, 0x00, // mov r9d,3
                0x45, 0x85, 0xc9, // test r9d,r9d
                0x41, 0x0f, 0x9a, 0xc2, // setp r10b
                0x9f, // lahf
                0xf9, // stc
                0xf5, // cmc
                0x41, 0x0f, 0x92, 0xc3, // setc r11b
                0xc3, // ret
            ],
            &[],
        ));
        assert_eq!(emu.register("rbx"), Some(0x4433_2211));
        assert_eq!(emu.register("rcx"), Some(0x0807_0605_0403_0201));
        assert_eq!(
            emu.register("rsi"),
            Some(0xa000_000f),
            "edi's low bits fill from the top"
        );
        assert_eq!(
            emu.register("r8"),
            Some(0),
            "bit 3 of 0xf1 was shifted out last"
        );
        assert_eq!(emu.register("r10"), Some(1), "3 has an even count of ones");
        assert_eq!(
            emu.register("rax"),
            Some(0x061f),
            "shld made eax 0x1f; lahf put PF and the fixed bit in ah"
        );
        assert_eq!(
            emu.register("r11"),
            Some(0),
            "cmc flipped the carry stc set"
        );
    }
}
