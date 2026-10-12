//! The instruction sets the engine decodes, one module each.
//!
//! [`x86`] carries x86 and x86-64 (iced-x86). No module outside `isa` names
//! a decoder crate: consumers import an instruction set's names from its
//! module here, so a decoder's types stop at this boundary.

pub mod x86;
