//! The instruction sets the engine decodes, one module each.
//!
//! [`x86`] carries x86 and x86-64 (iced-x86) and [`a64`] carries AArch64
//! (yaxpeax-arm). No module outside `isa` names a decoder crate: consumers
//! import an instruction set's names from its module here, so a decoder's
//! types stop at this boundary. [`Isa`] is the engine-owned name for which
//! of them a program's code is written in.

pub mod a64;
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
}
