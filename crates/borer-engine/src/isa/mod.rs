//! The instruction sets the engine decodes, one module each.
//!
//! [`x86`] carries x86 and x86-64 (iced-x86), [`a64`] carries AArch64
//! (yaxpeax-arm), [`a32`] carries ARM32's A32 and T32 and [`rv`] carries
//! RISC-V's RV32GC and RV64GC (the last two the engine's own decoders). No module outside `isa` names a decoder crate: consumers
//! import an instruction set's names from its module here, so a decoder's
//! types stop at this boundary. [`Isa`] is the engine-owned name for which
//! of them a program's code is written in.

pub mod a32;
pub mod a64;
pub mod rv;
pub mod x86;

/// An instruction set the engine knows how to decode, with what its decoder
/// needs to be told.
///
/// [`crate::program::Arch::isa`] maps an architecture to one; code that
/// dispatches on the instruction set matches on this rather than reading
/// the decoder width off [`crate::program::Arch::bitness`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Isa {
    /// x86 or x86-64, decoded by iced-x86.
    X86 {
        /// Decoder bitness: `32` or `64`.
        bits: u32,
    },
    /// AArch64 (arm64): fixed-width four-byte little-endian instructions.
    A64,
    /// ARM32: four-byte A32 and two- or four-byte T32 little-endian
    /// instructions, which at which address told by the program's
    /// [`a32::Modes`].
    A32,
    /// RISC-V: four-byte instructions and two-byte compressed ones, little
    /// endian, with registers of the width named.
    Rv(rv::Xlen),
}

impl Isa {
    /// Returns the width of its general registers in bits: `32` or `64`.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            Isa::X86 { bits } => bits,
            Isa::A64 => 64,
            Isa::A32 => 32,
            Isa::Rv(xlen) => xlen.bits(),
        }
    }
}
