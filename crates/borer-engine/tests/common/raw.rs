//! A raw two-section image at a PE's base, for tests that hand-assemble
//! one function: `.text` at 0x401000, entered there, and a read-only
//! `.rdata` at 0x402000, each a page.

use borer_engine::program::{Arch, Program, Section};

/// Builds a raw image with `code` in `.text` at 0x401000, entered there,
/// and `data` in a read-only `.rdata` at 0x402000.
///
/// The base keeps small constants out of the mapped range, as a PE's does.
///
/// # Arguments
///
/// * `arch` - The instruction set `code` is written in.
/// * `code` - The bytes of `.text`, at most a page.
/// * `data` - The bytes of `.rdata`, at most a page.
///
/// # Panics
///
/// When `code` or `data` exceeds a page.
pub(crate) fn image(arch: Arch, code: &[u8], data: &[u8]) -> Program {
    let mut bytes = vec![0u8; 0x2000];
    bytes[..code.len()].copy_from_slice(code);
    bytes[0x1000..0x1000 + data.len()].copy_from_slice(data);
    Program::raw(
        bytes,
        arch,
        0x400000,
        Some(0x401000),
        vec![
            Section::mapped(".text", 0x401000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x402000, 0x1000, 0x1000, false, false),
        ],
    )
}
