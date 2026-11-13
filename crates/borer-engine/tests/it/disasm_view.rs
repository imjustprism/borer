//! Function disassembly views: one renderer writes the plain listing and
//! the typed [`View`], so [`View::spell`] matches [`disasm_function`] and
//! every link comes from the decoder.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{Bytes, disasm_function, disasm_view};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
use borer_engine::view::{Kind, Ref, View};

/// Code section base of the x64 fixture.
const TEXT: u64 = 0x1_4000_1000;
/// Read-only data section base of the x64 fixture.
const RDATA: u64 = 0x1_4000_2000;
/// Import slot address inside `.rdata`.
const SLOT: u64 = 0x1_4000_2000;
/// Read-only global address inside `.rdata`.
const DATA: u64 = 0x1_4000_2008;
/// Helper function entry in `.text`.
const HELPER: u64 = 0x1_4000_1040;

/// Token triple `(text, kind, ref)` for one token of a view line.
type Tok<'a> = (&'a str, Kind, Option<Ref>);

/// Returns one line's tokens as `(text, kind, ref)` triples.
///
/// # Arguments
///
/// * `v` - The view.
/// * `i` - Line index.
fn line_tokens(v: &View, i: usize) -> Vec<Tok<'_>> {
    let line = v.line(i).expect("line exists");
    v.tokens(i)
        .map(|(span, kind, link)| (&line[span], kind, link.cloned()))
        .collect()
}

/// Builds a two-section PE x64 image with code runs in `.text` and symbols.
///
/// # Arguments
///
/// * `runs` - `(va, bytes)` pairs placed inside `.text`.
/// * `symbols` - Symbols attached to the program.
fn x64_image(runs: &[(u64, &[u8])], symbols: Vec<Symbol>) -> Program {
    let mut bytes = vec![0u8; 0x2000];
    bytes[..0x1000].fill(0xcc);
    for &(va, code) in runs {
        let off = usize::try_from(va - TEXT).expect("in .text");
        bytes[off..off + code.len()].copy_from_slice(code);
    }
    let sections = vec![
        Section::mapped(".text", TEXT, 0, 0x1000, false, true),
        Section::mapped(".rdata", RDATA, 0x1000, 0x1000, false, false),
    ];
    let mut p = Program::raw(bytes, Arch::X86_64, 0x1_4000_0000, Some(TEXT), sections);
    p.format = BinaryFormat::Pe;
    p.symbols = symbols;
    p
}

/// Builds the six-instruction x64 fixture covering a direct call, an import
/// slot call, a `rip`-relative load, `rep movsb`, a conditional jump and a
/// `jmp short`.
fn x64_fixture() -> (Program, Analysis) {
    let main_code: &[u8] = &[
        // ASM: call 0x140001040
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call qword [rel 0x140002000]
        0xff, 0x15, 0xf5, 0x0f, 0x00, 0x00, // ASM: mov rax, [rel 0x140002008]
        0x48, 0x8b, 0x05, 0xf6, 0x0f, 0x00, 0x00, // ASM: rep movsb
        0xf3, 0xa4, // ASM: jne short 0x140001018
        0x75, 0x02, // ASM: jmp short 0x140001040
        0xeb, 0x28, // ASM: ret
        0xc3,
    ];
    let helper_code: &[u8] = &[
        // ASM: ret
        0xc3,
    ];
    let symbols = vec![
        Symbol {
            name: "helper".to_owned(),
            addr: HELPER,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "KERNEL32.dll!GetTickCount".to_owned(),
            addr: SLOT,
            kind: SymbolKind::Import,
        },
    ];
    let p = x64_image(&[(TEXT, main_code), (HELPER, helper_code)], symbols);
    let a = Analysis::compute(&p);
    (p, a)
}

/// Finds the first line starting with `prefix` and returns its index and tokens.
///
/// # Arguments
///
/// * `v` - The view.
/// * `prefix` - Line prefix to match.
fn line_starting<'a>(v: &'a View, prefix: &str) -> (usize, Vec<Tok<'a>>) {
    let i = (0..v.lines())
        .find(|&i| v.line(i).unwrap_or_default().starts_with(prefix))
        .expect("matching line");
    (i, line_tokens(v, i))
}

/// Every x64 call, import-slot and `rip`-relative operand in the listing view
/// carries its exact [`Kind`] and [`Ref`], and [`View::spell`] matches
/// [`disasm_function`] with and without the bytes column.
#[test]
fn x64_listing_view_tokens_and_spell_match_text() {
    let (p, a) = x64_fixture();
    let o = Overlay::default();
    for (flag, mode) in [(false, Bytes::Hidden), (true, Bytes::Shown)] {
        let text = disasm_function(&p, &a, &o, TEXT, 100, flag).expect("text");
        let view = disasm_view(&p, &a, &o, TEXT, 100, mode).expect("view");
        assert_eq!(view.spell(), text, "bytes={flag}");
    }
    let v = disasm_view(&p, &a, &o, TEXT, 100, Bytes::Hidden).expect("view");
    assert_eq!(
        line_tokens(&v, 0),
        vec![(
            "// sub_140001000 @ 0x140001000: 7 instructions, 5 blocks",
            Kind::Comment,
            None,
        )]
    );
    assert_eq!(
        line_starting(&v, "0x140001000").1,
        vec![
            ("0x140001000", Kind::Address, Some(Ref::Address(TEXT))),
            ("  ", Kind::Space, None),
            ("call", Kind::Mnemonic, None),
            (" ", Kind::Space, None),
            ("0000000140001040h", Kind::Address, Some(Ref::Function(HELPER))),
            ("  ", Kind::Space, None),
            ("; ", Kind::Comment, None),
            ("helper", Kind::Function, Some(Ref::Function(HELPER))),
        ]
    );
    assert_eq!(
        line_starting(&v, "0x140001005").1,
        vec![
            ("0x140001005", Kind::Address, Some(Ref::Address(TEXT + 5))),
            ("  ", Kind::Space, None),
            ("call", Kind::Mnemonic, None),
            (" ", Kind::Space, None),
            ("qword", Kind::Keyword, None),
            (" ", Kind::Space, None),
            ("[", Kind::Punct, None),
            ("rel", Kind::Keyword, None),
            (" ", Kind::Space, None),
            ("140002000h", Kind::Number, Some(Ref::Address(SLOT))),
            ("]", Kind::Punct, None),
            ("  ", Kind::Space, None),
            ("; ", Kind::Comment, None),
            (
                "KERNEL32.dll!GetTickCount",
                Kind::Function,
                Some(Ref::Import(SLOT)),
            ),
        ]
    );
    assert_eq!(
        line_starting(&v, "0x14000100b").1,
        vec![
            ("0x14000100b", Kind::Address, Some(Ref::Address(TEXT + 0xb))),
            ("  ", Kind::Space, None),
            ("mov", Kind::Mnemonic, None),
            (" ", Kind::Space, None),
            ("rax", Kind::Register, None),
            (",", Kind::Punct, None),
            ("[", Kind::Punct, None),
            ("rel", Kind::Keyword, None),
            (" ", Kind::Space, None),
            ("140002008h", Kind::Number, Some(Ref::Address(DATA))),
            ("]", Kind::Punct, None),
        ]
    );
}

/// Prefixed instructions, conditional branches, block labels and `jmp short`
/// in the x64 listing view carry exact token kinds and links.
#[test]
fn x64_listing_view_branches_labels_and_prefixes() {
    let (p, a) = x64_fixture();
    let v = disasm_view(&p, &a, &Overlay::default(), TEXT, 100, Bytes::Hidden).expect("view");
    let addr = |off: u64| Some(Ref::Address(TEXT + off));
    assert_eq!(
        line_starting(&v, "0x140001012").1,
        vec![
            ("0x140001012", Kind::Address, addr(0x12)),
            ("  ", Kind::Space, None),
            ("rep", Kind::Keyword, None),
            (" ", Kind::Space, None),
            ("movsb", Kind::Mnemonic, None),
        ]
    );
    assert_eq!(
        line_starting(&v, "0x140001014").1,
        vec![
            ("0x140001014", Kind::Address, addr(0x14)),
            ("  ", Kind::Space, None),
            ("jne", Kind::Mnemonic, None),
            (" ", Kind::Space, None),
            ("short", Kind::Keyword, None),
            (" ", Kind::Space, None),
            ("0000000140001018h", Kind::Address, addr(0x18)),
        ]
    );
    let (label_idx, label_toks) = line_starting(&v, "L_140001016");
    assert_eq!(
        label_toks,
        vec![
            ("L_140001016", Kind::Label, addr(0x16)),
            (":", Kind::Punct, None),
        ]
    );
    assert_eq!(
        line_starting(&v, "0x140001016").1,
        vec![
            ("0x140001016", Kind::Address, addr(0x16)),
            ("  ", Kind::Space, None),
            ("jmp", Kind::Mnemonic, None),
            (" ", Kind::Space, None),
            ("short", Kind::Keyword, None),
            (" ", Kind::Space, None),
            ("0000000140001040h", Kind::Address, Some(Ref::Function(HELPER))),
        ]
    );
    assert_eq!(v.definition(&Ref::Address(TEXT + 0x16)), Some(label_idx));
}

/// A RIP-relative memory operand under an `fs:` or `gs:` override leaves its
/// displacement unlinked because the segment base is unknown.
#[test]
fn segment_prefixed_rip_relative_load_stays_unlinked() {
    let code: &[u8] = &[
        // ASM: mov rax, [gs:rel 0x140001018]
        0x65, 0x48, 0x8b, 0x05, 0x10, 0x00, 0x00, 0x00, // ASM: ret
        0xc3,
    ];
    let p = x64_image(&[(TEXT, code)], Vec::new());
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = disasm_function(&p, &a, &o, TEXT, 100, false).expect("text");
    let v = disasm_view(&p, &a, &o, TEXT, 100, Bytes::Hidden).expect("view");
    assert_eq!(v.spell(), text);
    let load_line = line_starting(&v, "0x140001000").1;
    assert!(
        load_line.contains(&("gs", Kind::Register, None)),
        "{load_line:?}"
    );
    assert!(
        load_line.contains(&("140001018h", Kind::Number, None)),
        "{load_line:?}"
    );
    assert!(
        load_line.iter().skip(1).all(|(_, _, r)| r.is_none()),
        "{load_line:?}"
    );
}

/// A branch target that is no function start links as [`Ref::Address`]; one
/// where a function starts links as [`Ref::Function`], including when an
/// overlay name annotates a non-function target.
#[test]
fn branch_target_links_distinguish_functions_from_addresses() {
    let main_code: &[u8] = &[
        // ASM: je 0x14000100b
        0x0f, 0x84, 0x05, 0x00, 0x00, 0x00, // ASM: jmp 0x140001040
        0xe9, 0x35, 0x00, 0x00, 0x00, // ASM: ret
        0xc3,
    ];
    let helper_code: &[u8] = &[
        // ASM: ret
        0xc3,
    ];
    let symbols = vec![Symbol {
        name: "helper".to_owned(),
        addr: HELPER,
        kind: SymbolKind::Export,
    }];
    let p = x64_image(&[(TEXT, main_code), (HELPER, helper_code)], symbols);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(TEXT + 0xb, "done\nline".to_owned());
    o.comments.insert(TEXT, "note\nhere".to_owned());

    let text = disasm_function(&p, &a, &o, TEXT, 100, false).expect("text");
    let v = disasm_view(&p, &a, &o, TEXT, 100, Bytes::Hidden).expect("view");
    assert_eq!(v.spell(), text);
    for i in 0..v.lines() {
        assert!(!v.line(i).unwrap_or_default().contains('\n'));
    }
    let je_line = line_starting(&v, "0x140001000").1;
    assert!(
        je_line.contains(&("000000014000100Bh", Kind::Address, Some(Ref::Address(TEXT + 0xb)))),
        "{je_line:?}"
    );
    let jmp_line = line_starting(&v, "0x140001006").1;
    assert!(
        jmp_line.contains(&("0000000140001040h", Kind::Address, Some(Ref::Function(HELPER)))),
        "{jmp_line:?}"
    );
    assert!(
        jmp_line.contains(&("helper", Kind::Function, Some(Ref::Function(HELPER)))),
        "{jmp_line:?}"
    );
}

