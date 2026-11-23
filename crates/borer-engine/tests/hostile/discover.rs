//! Discovery sums the sizes a file states without overflowing.
//!
//! An ELF whose function symbols claim more bytes together than the address
//! space holds is read, and its sizes are summed saturating, never past
//! `u64::MAX` (a mutation of a corpus library found the sum trap under
//! overflow checks).

use std::path::PathBuf;

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;

use super::{elfgen, serial};

/// Two function symbols of 2^63 bytes each load and are discovered
/// without the sum of their sizes overflowing.
///
/// # Panics
///
/// When the image does not load, the sum overflows, or the entry is not
/// discovered.
#[test]
fn function_sizes_past_the_address_space_sum_without_overflow() {
    let _held = serial();
    let mut symtab = vec![0u8; 24];
    for k in 0..2u64 {
        symtab.extend(elfgen::sym_sized(1, 0x12, 1, 0x1000 + k, 1 << 63));
    }
    let code = vec![0xc3; 0x10];
    let mut secs = vec![
        elfgen::Sec::new(".text", elfgen::PROGBITS, elfgen::AX, 0x1000, code),
        elfgen::Sec::new(".symtab", elfgen::SYMTAB, 0, 0x2000, symtab),
        elfgen::Sec::new(".strtab", elfgen::STRTAB, 0, 0x3000, b"\0f\0".to_vec()),
    ];
    secs[1].link = 3;
    secs[1].info = 1;
    secs[1].entsize = 24;
    let bytes = elfgen::build(elfgen::ET_EXEC, elfgen::EM_X86_64, 0x1000, &secs);
    let p = Program::from_bytes(PathBuf::from("sizes.elf"), bytes).expect("the image loads");
    assert!(p.function_ranges.len() >= 2, "{:?}", p.function_ranges);
    let a = Analysis::compute(&p);
    assert!(a.function(0x1000).is_some());
}
