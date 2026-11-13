//! The lines a `decompile` answer carries under its first line, and the
//! index's form of the answer.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::{checked_header, decompile_named, shown, with_header};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

/// A raw x86-64 image of `code` in `.text` at 0x1000, entered there.
///
/// # Arguments
///
/// * `code` - The section's bytes.
fn image(code: Vec<u8>) -> Program {
    let len = u64::try_from(code.len()).expect("small");
    let text = Section::mapped(".text", 0x1000, 0, len, false, true);
    Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text])
}

/// The index's form of an answer is `None` without a body, and otherwise
/// the body with the check line, then the warning, under its first line.
///
/// 0x1000 calls `_callee` at 0x1010, which the text gives no prototype,
/// so the warning names it. The warning and the next lines read the body
/// they are given, the check line the memo: a body that calls nothing gets
/// the same check line and no warning.
#[test]
fn the_index_form_puts_the_check_and_the_warning_under_the_first_line() {
    let mut code = vec![
        0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend([
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ]);
    code.resize(0x20, 0xcc);
    let mut p = image(code);
    p.symbols = vec![Symbol {
        name: "_callee".to_owned(),
        addr: 0x1010,
        kind: SymbolKind::Local,
    }];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(shown(&p, &a, &o, 0x1000, None), None);
    assert_eq!(shown(&p, &a, &o, 0x1000, Some("")), None);
    let check = checked_header(&p, &a, &o, 0x1000).expect("a check line");
    assert!(
        check.starts_with("// checked vs binary: statements as emitted, "),
        "{check}"
    );
    let warn =
        "// warn: callee _callee: no prototype in the text, so arguments and result are guesses";
    let body = decompile_named(&p, &a, &o, 0x1000).expect("a body");
    assert_eq!(
        shown(&p, &a, &o, 0x1000, Some(&body)),
        Some(with_header(&body, Some(&format!("{check}\n{warn}"))))
    );
    assert_eq!(
        shown(&p, &a, &o, 0x1000, Some("// f\nreturn;\n")),
        Some(format!("// f\n{check}\nreturn;\n"))
    );
}
