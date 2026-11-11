//! DWARF read from bytes a compiler wrote, not from bytes built with the
//! reader's own constants.
//!
//! The sections are clang 23.1.5's for
//! `int scale(int amount) { int doubled = amount * 2; return doubled + 1; }`,
//! built with `--target=x86_64-unknown-linux-gnu -O0 -g -gdwarf-4
//! -fno-omit-frame-pointer -ffreestanding -nostdlib -static -fuse-ld=lld
//! -Wl,-e,scale -Wl,--build-id=none -Wl,--image-base=0 -Wl,-Ttext=0x1000
//! -fdebug-compilation-dir=.` and copied out whole. Read by hand: the
//! subprogram's abbreviation states `DW_AT_frame_base` (0x40) as an
//! `exprloc` holding `DW_OP_reg6` (`rbp`), and `doubled` is a
//! `DW_TAG_variable` at `DW_OP_fbreg -8`, the slot `mov [rbp-8], eax`
//! writes.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::elfgen::{self, AX, EM_X86_64, ET_EXEC, PROGBITS, Sec};
use borer_engine::program::Program;

/// `.text`: `scale`, at 0x1000.
const TEXT: [u8; 23] = [
    0x55, 0x48, 0x89, 0xe5, 0x89, 0x7d, 0xfc, 0x8b, 0x45, 0xfc, 0xd1, 0xe0, 0x89, 0x45, 0xf8, 0x8b,
    0x45, 0xf8, 0x83, 0xc0, 0x01, 0x5d, 0xc3,
];

/// `.debug_abbrev`.
const ABBREV: [u8; 84] = [
    0x01, 0x11, 0x01, 0x25, 0x0e, 0x13, 0x05, 0x03, 0x0e, 0x10, 0x17, 0x1b, 0x0e, 0x11, 0x01, 0x12,
    0x06, 0x00, 0x00, 0x02, 0x2e, 0x01, 0x11, 0x01, 0x12, 0x06, 0x40, 0x18, 0x03, 0x0e, 0x3a, 0x0b,
    0x3b, 0x0b, 0x27, 0x19, 0x49, 0x13, 0x3f, 0x19, 0x00, 0x00, 0x03, 0x05, 0x00, 0x02, 0x18, 0x03,
    0x0e, 0x3a, 0x0b, 0x3b, 0x0b, 0x49, 0x13, 0x00, 0x00, 0x04, 0x34, 0x00, 0x02, 0x18, 0x03, 0x0e,
    0x3a, 0x0b, 0x3b, 0x0b, 0x49, 0x13, 0x00, 0x00, 0x05, 0x24, 0x00, 0x03, 0x0e, 0x3e, 0x0b, 0x0b,
    0x0b, 0x00, 0x00, 0x00,
];

/// `.debug_info`.
const INFO: [u8; 104] = [
    0x64, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x01, 0x23, 0x00, 0x00, 0x00,
    0x1d, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x00, 0x00, 0x00, 0x00, 0x10,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x17, 0x00, 0x00, 0x00, 0x02, 0x00, 0x10, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x17, 0x00, 0x00, 0x00, 0x01, 0x56, 0x11, 0x00, 0x00, 0x00, 0x01, 0x01, 0x60,
    0x00, 0x00, 0x00, 0x03, 0x02, 0x91, 0x7c, 0x00, 0x00, 0x00, 0x00, 0x01, 0x01, 0x60, 0x00, 0x00,
    0x00, 0x04, 0x02, 0x91, 0x78, 0x17, 0x00, 0x00, 0x00, 0x01, 0x02, 0x60, 0x00, 0x00, 0x00, 0x00,
    0x05, 0x1f, 0x00, 0x00, 0x00, 0x05, 0x04, 0x00,
];

/// `.debug_str`.
const STR: &[u8; 136] = b"amount\0scale.c\0.\0scale\0doubled\0int\0\
clang version 23.1.5 (https://github.com/llvm/llvm-project \
392dfff97d29b59d77e5cac6d4b6ef2585fe7117)\0";

/// Builds an image holding `scale` and the given debug sections.
///
/// # Arguments
///
/// * `info` - `.debug_info`.
/// * `abbrev` - `.debug_abbrev`.
///
/// # Returns
///
/// The image's bytes.
fn scale(info: &[u8], abbrev: &[u8]) -> Vec<u8> {
    elfgen::build(
        ET_EXEC,
        EM_X86_64,
        0x1000,
        &[
            Sec::new(".text", PROGBITS, AX, 0x1000, TEXT.to_vec()),
            Sec::new(".debug_info", PROGBITS, 0, 0x2000, info.to_vec()),
            Sec::new(".debug_abbrev", PROGBITS, 0, 0x3000, abbrev.to_vec()),
            Sec::new(".debug_str", PROGBITS, 0, 0x4000, STR.to_vec()),
        ],
    )
}

/// The local a compiler placed under `rbp` lands on its frame slot: the
/// frame base is a word under the entry stack pointer, so `rbp - 8` is
/// slot `-0x10`.
#[test]
fn a_compiled_local_lands_on_its_frame_slot() {
    let p = Program::from_bytes("scale.elf".into(), scale(&INFO, &ABBREV)).expect("it loads");
    let f = p
        .debug_functions
        .iter()
        .find(|d| d.low_pc == 0x1000)
        .expect("the debug information states scale");
    assert_eq!(f.name, "scale");
    assert_eq!(f.locals.get(&-0x10).map(String::as_str), Some("doubled"));
}

/// A frame base stated as `DW_OP_regx 6` (0x90, then the register) names
/// `rbp` as `DW_OP_reg6` does.
///
/// The compiled unit's one-byte frame base grows by a byte: the unit and
/// the entry's expression each state one more, and the type references
/// past it move up by one.
#[test]
fn a_regx_frame_base_names_the_frame_pointer() {
    let mut info = INFO.to_vec();
    info.splice(55..57, [0x02, 0x90, 0x06]);
    info[0] += 1;
    for at in [63, 77, 91] {
        info[at] += 1;
    }
    let p = Program::from_bytes("regx.elf".into(), scale(&info, &ABBREV)).expect("it loads");
    let locals: Vec<_> = p.debug_functions.iter().map(|d| &d.locals).collect();
    assert_eq!(locals.len(), 1);
    assert_eq!(locals[0].get(&-0x10).map(String::as_str), Some("doubled"));
}
