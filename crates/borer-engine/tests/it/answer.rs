//! The answer `decompile` gives, the lines it carries under its first
//! line, and the index's form of it.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::replay::TextCheck;
use borer_engine::analysis::decompile::{
    Detail, Site, answer, answer_header, checked_header, decompile_named, shown, skeleton,
    with_header,
};
use borer_engine::analysis::render::{Budget, Counterexample, Repair};
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

/// An image whose function at 0x1000 compares its first argument against
/// a constant: the check does not flag it, and a next step points `solve`
/// at it.
fn compare() -> Program {
    let mut code = vec![
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    image(code)
}

/// Fills the memo as if the text check had flagged 0x1000 under `o` and
/// the repair search there had ended with `repair`.
///
/// No committed fixture is flagged, so a test of the flagged answer plants
/// both results before anything reads them; a cell is found by its kind,
/// the names, the key and the value's type, so these are the ones
/// [`checked_header`] and the search read.
///
/// # Arguments
///
/// * `a` - An analysis nothing has read the function through yet.
/// * `o` - The names the answer is asked under.
/// * `repair` - What the search is to have ended with.
fn flag(a: &Analysis, o: &Overlay, repair: Repair) {
    let check = TextCheck {
        blocks: 1,
        checked: 1,
        disagree: vec![0x1000],
        ..TextCheck::default()
    };
    let names = o.fingerprint();
    a.derived
        .get_or_build_item("text_check", names, 0x1000_u64, || Some(check), |_| 0);
    let key = (0x1000_u64, Budget::ANSWER);
    a.derived
        .get_or_build_item("repair", names, key, || repair, |_| 0);
}

/// An answer is the named text with its header under the first line: the
/// check line, then the next step.
///
/// Its outline is the skeleton of that text under the same lines, and an
/// address no function starts at has no answer.
#[test]
fn an_answer_puts_its_header_under_the_text_at_either_detail() {
    let p = compare();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let full = answer(&p, &a, &o, 0x1000, Detail::Full).expect("an answer");
    let lines: Vec<&str> = full.lines().collect();
    assert!(
        lines.get(1).is_some_and(|l| {
            l.starts_with("// checked vs binary: statements as emitted, 1/1 blocks")
                && !l.contains("disagree")
        }),
        "{full}"
    );
    assert_eq!(
        lines.get(2).copied(),
        Some(
            "// next: borer://solve/0x1000,a1 (compares against 0x1337abcd: solve tries it as a1)"
        ),
        "{full}"
    );
    let header = answer_header(&p, &a, &o, 0x1000, None);
    let body = decompile_named(&p, &a, &o, 0x1000).expect("a body");
    assert_eq!(full, with_header(&body, header.as_deref()));
    assert_eq!(
        answer(&p, &a, &o, 0x1000, Detail::Skeleton),
        Some(with_header(&skeleton(&body), header.as_deref()))
    );
    assert!(answer(&p, &a, &o, 0x1001, Detail::Full).is_none());
}

/// A flagged function's `// warn:` line ends with the repair search's note
/// only when the search leaves a value that differs.
///
/// A function only the replay disagrees with gets no note, and the index's
/// form, made without the search, carries none either way.
#[test]
fn a_flagged_answer_carries_the_note_only_for_a_value_that_differs() {
    let p = compare();
    let o = Overlay::default();
    let differs = |input: &str, line: &str, why: &str| Repair::Disagrees {
        at: Counterexample {
            input: input.to_owned(),
            line: line.to_owned(),
            why: why.to_owned(),
        },
        tried: Vec::new(),
        checks: 1,
    };
    let flagged = |a: &Analysis| {
        let text = answer(&p, a, &o, 0x1000, Detail::Full).expect("an answer");
        let body = decompile_named(&p, a, &o, 0x1000).expect("a body");
        let indexed = shown(&p, a, &o, 0x1000, Some(&body)).expect("an index form");
        assert!(
            text.lines()
                .nth(1)
                .is_some_and(|l| l.contains("disagree at 0x1000")),
            "{text}"
        );
        assert!(
            indexed.contains("disagree at 0x1000") && !indexed.contains("differs on"),
            "{indexed}"
        );
        text
    };
    let value = differs("0x10", "return a1;", "the text returns 0x1, the binary 0x2");
    let note = value.note().expect("a value that differs is noted");
    let a = Analysis::compute(&p);
    flag(&a, &o, value);
    let text = flagged(&a);
    assert!(
        text.lines()
            .nth(2)
            .is_some_and(|l| l.starts_with("// warn:") && l.ends_with(note.as_str())),
        "{text}"
    );
    let why = "the statements of 0x1000 disagree with the machine";
    let a = Analysis::compute(&p);
    flag(&a, &o, differs("the replay's states", "", why));
    let text = flagged(&a);
    assert!(!text.contains("differs on"), "{text}");
}

/// The repair search's rendering is shown only where the text check flags
/// the function, and its check line is the check of that rendering.
///
/// The search would mask the quotient 0x1000 returns to its lane, which
/// the text widens by its sign; the replay bears the text out, so the
/// answer is the plain text. The memo is then filled as if the check had
/// flagged it and the search had kept the mask.
#[test]
fn only_a_flagged_answer_shows_the_rendering_the_search_kept() {
    let mut code = vec![
        0x89, 0xc8, // ASM: mov eax, ecx
        0xb9, 0xfb, 0xff, 0xff, 0xff, // ASM: mov ecx, 0xfffffffb
        0x99, // ASM: cdq
        0xf7, 0xf9, // ASM: idiv ecx
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    let p = image(code);
    let o = Overlay::default();
    let a = Analysis::compute(&p);
    let header = answer_header(&p, &a, &o, 0x1000, None);
    let plain = decompile_named(&p, &a, &o, 0x1000).expect("a body");
    assert!(!plain.contains("& 0xffffffff;"), "{plain}");
    assert_eq!(
        answer(&p, &a, &o, 0x1000, Detail::Full),
        Some(with_header(&plain, header.as_deref()))
    );
    let a = Analysis::compute(&p);
    let kept = Repair::Repaired {
        moved: vec![Site::Return],
        tried: Vec::new(),
        checks: 1,
    };
    flag(&a, &o, kept);
    let text = answer(&p, &a, &o, 0x1000, Detail::Full).expect("an answer");
    assert!(text.contains("& 0xffffffff;"), "{text}");
    assert!(
        text.lines()
            .nth(1)
            .is_some_and(|l| l.starts_with("// checked vs binary") && !l.contains("disagree")),
        "{text}"
    );
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
