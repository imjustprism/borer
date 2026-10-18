//! The string instructions (`movs`, `stos`, `lods`, `scas`, `cmps`) and
//! their `rep` prefixes.

use super::{Emulator, Stop, mask, sized_ax, width_bits};
use crate::isa::x86::{Instruction, Mnemonic, Register};
use crate::num::from_usize;

/// Most iterations one `rep` string instruction runs before it reads as a
/// runaway on uninitialized state and stops the run.
const REP_MAX: u64 = 0x0400_0000;

/// A string instruction: what one step does between `[rsi]`, `[rdi]` and
/// the accumulator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum StringOp {
    /// `movs`: copies an element from `[rsi]` to `[rdi]`.
    Movs,
    /// `stos`: stores the accumulator at `[rdi]`.
    Stos,
    /// `lods`: loads the accumulator from `[rsi]`.
    Lods,
    /// `scas`: compares the accumulator with `[rdi]`.
    Scas,
    /// `cmps`: compares `[rsi]` with `[rdi]`.
    Cmps,
}

impl StringOp {
    /// The operation and element width a mnemonic names.
    ///
    /// # Arguments
    ///
    /// * `m` - The mnemonic.
    ///
    /// # Returns
    ///
    /// The operation and its element in bytes, or `None` when `m` is not a
    /// string instruction.
    pub(super) fn of(m: Mnemonic) -> Option<(StringOp, usize)> {
        Some(match m {
            Mnemonic::Movsb => (StringOp::Movs, 1),
            Mnemonic::Movsw => (StringOp::Movs, 2),
            Mnemonic::Movsd => (StringOp::Movs, 4),
            Mnemonic::Movsq => (StringOp::Movs, 8),
            Mnemonic::Stosb => (StringOp::Stos, 1),
            Mnemonic::Stosw => (StringOp::Stos, 2),
            Mnemonic::Stosd => (StringOp::Stos, 4),
            Mnemonic::Stosq => (StringOp::Stos, 8),
            Mnemonic::Lodsb => (StringOp::Lods, 1),
            Mnemonic::Lodsw => (StringOp::Lods, 2),
            Mnemonic::Lodsd => (StringOp::Lods, 4),
            Mnemonic::Lodsq => (StringOp::Lods, 8),
            Mnemonic::Scasb => (StringOp::Scas, 1),
            Mnemonic::Scasw => (StringOp::Scas, 2),
            Mnemonic::Scasd => (StringOp::Scas, 4),
            Mnemonic::Scasq => (StringOp::Scas, 8),
            Mnemonic::Cmpsb => (StringOp::Cmps, 1),
            Mnemonic::Cmpsw => (StringOp::Cmps, 2),
            Mnemonic::Cmpsd => (StringOp::Cmps, 4),
            Mnemonic::Cmpsq => (StringOp::Cmps, 8),
            _ => return None,
        })
    }
}

impl Emulator<'_> {
    /// Runs a string instruction, repeating it when it carries a `rep` prefix.
    ///
    /// `rep movs` is how a packer copies its decrypted payload into place, so
    /// modeling the string operations is what lets the run materialize a whole
    /// image rather than a handful of bytes. The direction flag chooses the
    /// step's sign; `repe`/`repne` forms stop early on the zero flag. In
    /// 32-bit code the pointers wrap at four gigabytes, as the processor's
    /// do. An implausibly large count reads as a runaway on uninitialized
    /// state and stops the run rather than spinning.
    ///
    /// Each iteration past the first spends a step of the budget (the
    /// instruction's own step pays for the first), so the budget bounds a
    /// run's string work as it bounds its instructions: a hostile `rep stos`
    /// under a budget of five once ran for over a second and wrote 750
    /// megabytes. An iteration the budget cannot pay for stops the run with
    /// the counter and pointers stepped as far as the iterations it paid
    /// for, where an interrupt would leave them.
    ///
    /// # Arguments
    ///
    /// * `i` - The string instruction.
    /// * `op` - What one step does.
    /// * `bytes` - The element width.
    ///
    /// # Errors
    ///
    /// A fault when a load or store leaves mapped memory, [`Stop::Budget`]
    /// when the budget runs out mid-repeat, and [`Stop::MemoryFull`] when
    /// memory would grow past its cap.
    pub(super) fn string_op(
        &mut self,
        i: &Instruction,
        op: StringOp,
        bytes: usize,
    ) -> Result<Option<u64>, Stop> {
        let size = from_usize(bytes);
        let bits = width_bits(bytes);
        let step = if self.flags_df {
            0u64.wrapping_sub(size)
        } else {
            size
        };
        let zf_sensitive = matches!(op, StringOp::Scas | StringOp::Cmps);
        let repe = zf_sensitive && i.has_repe_prefix();
        let repne = zf_sensitive && i.has_repne_prefix();
        let rep = i.has_rep_prefix() || i.has_repe_prefix() || i.has_repne_prefix();
        let mut count = if rep { self.reg(Register::RCX) } else { 1 };
        if count > REP_MAX {
            return Err(Stop::Unmodeled("rep count too large".to_owned()));
        }
        let mut paid = true;
        while count > 0 {
            if !paid {
                if self.steps >= self.budget {
                    return Err(Stop::Budget);
                }
                self.steps += 1;
            }
            paid = false;
            let si = self.reg(Register::RSI);
            let di = self.reg(Register::RDI);
            let (next_si, next_di) = (
                self.narrow(si.wrapping_add(step)),
                self.narrow(di.wrapping_add(step)),
            );
            match op {
                StringOp::Movs => {
                    let v = self.load(si, bytes)?;
                    self.write(di, v, bytes)?;
                    self.set_reg(Register::RSI, next_si);
                    self.set_reg(Register::RDI, next_di);
                }
                StringOp::Stos => {
                    self.write(di, self.reg(Register::RAX), bytes)?;
                    self.set_reg(Register::RDI, next_di);
                }
                StringOp::Lods => {
                    let v = self.load(si, bytes)?;
                    self.set_reg_sized(sized_ax(bytes), v);
                    self.set_reg(Register::RSI, next_si);
                }
                StringOp::Scas => {
                    let a = mask(self.reg(Register::RAX), bits);
                    let b = self.load(di, bytes)?;
                    self.set_flags(a.wrapping_sub(b), bits);
                    self.set_reg(Register::RDI, next_di);
                }
                StringOp::Cmps => {
                    let a = self.load(si, bytes)?;
                    let b = self.load(di, bytes)?;
                    self.set_flags(a.wrapping_sub(b), bits);
                    self.set_reg(Register::RSI, next_si);
                    self.set_reg(Register::RDI, next_di);
                }
            }
            count -= 1;
            if rep {
                self.set_reg(Register::RCX, count);
                if repe && !self.flags_zero {
                    break;
                }
                if repne && self.flags_zero {
                    break;
                }
            }
        }
        Ok(None)
    }
}
