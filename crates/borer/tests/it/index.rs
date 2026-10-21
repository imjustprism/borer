//! The decompilation index's key, read through the library.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer::index::index_key;
use borer_engine::pack::Packs;
use borer_engine::program::{Arch, Program, Section};

/// The same bytes mapped at another address key an index of their own.
///
/// A raw load states where its bytes sit (`base`, `regions`), so one file
/// is two programs at two bases: every entry, call target and address in
/// the text differs. The index was keyed by the bytes alone, so a `grep`
/// after loading the file at the second base read the first base's
/// functions and addresses.
#[test]
fn the_same_bytes_mapped_elsewhere_key_an_index_of_their_own() {
    // ASM: mov eax,42; ret
    let code = vec![0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3];
    let at = |base: u64| {
        let text = Section::mapped(".text", base, 0, 6, false, true);
        Program::raw(code.clone(), Arch::X86_64, 0, Some(base), vec![text])
    };
    let packs = Packs::default();
    assert_ne!(
        index_key(&at(0x1000), &packs),
        index_key(&at(0x2000), &packs)
    );
    assert_eq!(
        index_key(&at(0x1000), &packs),
        index_key(&at(0x1000), &packs),
        "the key of one load is stable"
    );
}
