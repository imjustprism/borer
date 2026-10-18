//! Fields below a pointer: a callee handed a pointer into the middle of a
//! struct reads the members before it at negative offsets, and every
//! layout keeps them there.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::decompiled::decompiled;
use crate::raw;
use borer_engine::analysis::classes::fields_tsv;
use borer_engine::analysis::render::layout_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program};

/// Where [`raw::image`] enters the code.
const ENTRY: u64 = 0x401000;

/// Sums seven qwords around `rdx`: three below it and four from it up.
///
/// # Returns
///
/// The raw image.
fn middle_pointer() -> Program {
    let code: &[u8] = &[
        // ASM: mov rax, [rdx-0x40]
        0x48, 0x8b, 0x42, 0xc0, // ASM: add rax, [rdx-0x38]
        0x48, 0x03, 0x42, 0xc8, // ASM: add rax, [rdx-0x30]
        0x48, 0x03, 0x42, 0xd0, // ASM: add rax, [rdx]
        0x48, 0x03, 0x02, // ASM: add rax, [rdx+0x8]
        0x48, 0x03, 0x42, 0x08, // ASM: add rax, [rdx+0x10]
        0x48, 0x03, 0x42, 0x10, // ASM: add rax, [rdx+0x18]
        0x48, 0x03, 0x42, 0x18, // ASM: ret
        0xc3,
    ];
    raw::image(Arch::X86_64, code, &[])
}

/// The layout header lists the members below the pointer at their negative
/// offsets, and the body names them as such.
///
/// Only the offsets from zero up used to reach the header, so `a2` read
/// as a plain struct starting at the pointer.
#[test]
fn a_layout_keeps_the_fields_below_its_pointer() {
    let out = decompiled(&middle_pointer(), ENTRY);
    assert!(
        out.contains(
            "// layout a2: -0x40 u64, -0x38 u64, -0x30 u64, 0x0 u64, 0x8 u64, 0x10 u64, 0x18 u64"
        ),
        "{out}"
    );
    for name in [
        "field_neg0x40",
        "field_neg0x38",
        "field_neg0x30",
        "field_0x0",
    ] {
        assert!(out.contains(&format!("a2->{name}")), "{name}:\n{out}");
    }
    assert!(!out.contains("(a2 - "), "{out}");
}

/// The `fields` table lists the members below the pointer at their
/// negative offsets instead of dropping them.
#[test]
fn the_fields_table_keeps_the_fields_below_its_pointer() {
    let p = middle_pointer();
    let a = Analysis::compute(&p);
    let tsv = fields_tsv(&p, &a, &Overlay::default(), ENTRY).expect("decompiles");
    for off in ["-0x40", "-0x38", "-0x30", "0x0", "0x18"] {
        assert!(tsv.contains(&format!("a2\t{off}\t8\tr\t")), "{off}:\n{tsv}");
    }
}

/// The `layout` resource follows `rdx` and reports the same offsets.
#[test]
fn the_layout_resource_keeps_the_fields_below_its_pointer() {
    let p = middle_pointer();
    let a = Analysis::compute(&p);
    let out = layout_tsv(&p, &a, &Overlay::default(), "0x401000,rdx").expect("follows rdx");
    for off in ["-0x40 ", "-0x38 ", "-0x30 ", "0x0 ", "0x18 "] {
        assert!(
            out.lines()
                .any(|l| l.starts_with(off) && l.contains(" read ")),
            "{off}:\n{out}"
        );
    }
}
