//! The thread block a machine plants and the segment register that reads it.
//!
//! Windows keeps the block under `gs` (64-bit) or `fs` (32-bit), glibc under
//! `fs` (x86-64) or `gs` (i386). The fields whose planted values a reader
//! can tell apart are the ones a replay of the block compares.

use super::{Emulator, TEB_LAYOUT_32, TEB_LAYOUT_64, TEB_SPAN};
use crate::isa::x86::Register;
use crate::program::BinaryFormat;

/// Where glibc keeps the stack canary on x86-64, in the thread block `fs`
/// points at.
pub(crate) const CANARY_FS: u64 = 0x28;

/// Where glibc keeps it on i386, under `gs`.
pub(crate) const CANARY_GS: u64 = 0x14;

/// The canary word a machine over an ELF image plants: one fixed value,
/// so every run reads the same, with its low byte zero as glibc's own is.
pub(super) const CANARY: u64 = 0x2f8d_4a6b_93c1_e500;

/// The fields of glibc's x86-64 thread block the machine plants, as
/// offsets from its base and widths in bytes: the canary.
const GLIBC_64: [(u64, u64); 1] = [(CANARY_FS, 8)];

/// The fields of glibc's i386 thread block the machine plants.
const GLIBC_32: [(u64, u64); 1] = [(CANARY_GS, 4)];

/// The fields of Windows' 64-bit thread block the machine plants with
/// values of their own: the stack's base and limit, the block's own
/// address and the process block's.
const WINDOWS_64: [(u64, u64); 4] = [
    (TEB_LAYOUT_64.stack_base, 8),
    (TEB_LAYOUT_64.stack_limit, 8),
    (TEB_LAYOUT_64.this, 8),
    (TEB_LAYOUT_64.peb, 8),
];

/// The fields of Windows' 32-bit thread block the machine plants.
const WINDOWS_32: [(u64, u64); 4] = [
    (TEB_LAYOUT_32.stack_base, 4),
    (TEB_LAYOUT_32.stack_limit, 4),
    (TEB_LAYOUT_32.this, 4),
    (TEB_LAYOUT_32.peb, 4),
];

/// The thread block a machine plants, as a reader of it sees it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ThreadBlock {
    /// The segment register that reads it.
    pub(crate) segment: Register,
    /// Its address: the segment's base.
    pub(crate) base: u64,
    /// The fields planted with values a reader can tell apart, as offsets
    /// from the base and widths in bytes; none for an image of no system
    /// the machine lays a block out for.
    pub(crate) fields: &'static [(u64, u64)],
}

impl ThreadBlock {
    /// Tells whether an address is one the machine planted as zero rather
    /// than as the system's own value: in the span planted for the thread
    /// and process blocks, in none of the fields.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    pub(crate) fn unmodeled(&self, at: u64) -> bool {
        at.checked_sub(self.base).is_some_and(|off| {
            off < TEB_SPAN && !self.fields.iter().any(|&(o, n)| (o..o + n).contains(&off))
        })
    }
}

impl Emulator<'_> {
    /// Returns the segment register the image's thread block is read
    /// through: `fs` on x86-64 Linux and on 32-bit Windows, `gs` on i386
    /// Linux and on 64-bit Windows, as on Windows for any other image.
    pub(super) fn thread_segment(&self) -> Register {
        match (self.program.format == BinaryFormat::Elf, self.bitness) {
            (true, 32) | (false, 64) => Register::GS,
            _ => Register::FS,
        }
    }

    /// Returns the thread block the machine plants: the segment that reads
    /// it, its address, and the fields planted with values of their own.
    #[must_use]
    pub(crate) fn thread_block(&self) -> ThreadBlock {
        let wide = self.bitness == 64;
        let fields: &'static [(u64, u64)] = match self.program.format {
            BinaryFormat::Elf if wide => &GLIBC_64,
            BinaryFormat::Elf => &GLIBC_32,
            BinaryFormat::Pe if wide => &WINDOWS_64,
            BinaryFormat::Pe => &WINDOWS_32,
            BinaryFormat::MachO | BinaryFormat::Archive | BinaryFormat::Raw => &[],
        };
        ThreadBlock {
            segment: self.thread_segment(),
            base: self.teb,
            fields,
        }
    }
}
