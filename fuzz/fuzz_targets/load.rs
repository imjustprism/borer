//! Loads arbitrary bytes as a binary: PE, ELF, Mach-O (with their DWARF),
//! a minidump, or raw code. Any input may be refused; none may panic,
//! hang or exhaust memory.

#![no_main]

use borer_engine::program::Program;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    _ = Program::from_bytes_with("fuzz".into(), data.to_vec(), false, None);
});
