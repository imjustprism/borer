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

/// The index stores the warning a `decompile` answer shows, on the same line.
///
/// # Panics
///
/// When the warning is missing, or its line is not the answer's line.
#[test]
fn the_index_stores_the_warning_the_decompile_answer_shows() {
    use borer::index::{Matcher, build, grep};
    use borer_engine::analysis::decompile::{self, decompile_named, with_header};
    use borer_engine::analysis::{Analysis, Overlay, render};
    use borer_engine::program::SymbolKind;
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
    let text = Section::mapped(".text", 0x1000, 0, 0x20, false, true);
    let mut program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
    program.symbols = vec![borer_engine::program::Symbol {
        name: "_callee".to_owned(),
        addr: 0x1010,
        kind: SymbolKind::Local,
    }];
    let analysis = Analysis::compute(&program);
    let overlay = Overlay::default();
    let index = build(&program, &analysis, &overlay);
    let stored = index
        .functions
        .iter()
        .find(|f| f.entry == 0x1000)
        .expect("the caller is indexed");
    let body = decompile_named(&program, &analysis, &overlay, 0x1000).expect("a body");
    let mut header: Vec<String> = decompile::checked_header(&program, &analysis, &overlay, 0x1000)
        .into_iter()
        .chain(
            analysis
                .incomplete
                .then(|| format!("//{}", render::INCOMPLETE_NOTE.trim_start_matches('#'))),
        )
        .collect();
    header.extend(decompile::warnings(
        &program, &analysis, &overlay, 0x1000, &body, None,
    ));
    header.extend(
        render::next_steps(&program, &analysis, &overlay, 0x1000)
            .iter()
            .map(|step| format!("// next: {step}")),
    );
    let joined = (!header.is_empty()).then(|| header.join("\n"));
    let shown = with_header(&body, joined.as_deref());
    assert_eq!(stored.text, shown);
    let hits = grep(&index, &Matcher::parse("// warn:").expect("a literal"), "");
    assert_eq!(hits.len(), 1, "{hits:?}\n{shown}");
    let at = shown
        .lines()
        .position(|line| line.contains("// warn:"))
        .expect("the warning is in the text");
    assert_eq!(hits[0].line_no, at + 1);
    assert!(hits[0].line.contains("callee _callee"), "{}", hits[0].line);
}
