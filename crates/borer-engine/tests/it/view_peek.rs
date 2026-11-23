//! What a hover shows of a referent beyond its name: a function's head
//! with the lines it leaves out, a global's bytes as its type or a row of
//! hex, an import's declaration with how sure its name is.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::view::peek::{
    Certainty, Head, PEEK_BYTES, PEEK_LINES, PEEK_WIDTH, Peek, Read, peek,
};
use borer_engine::analysis::decompile::view::view;
use borer_engine::analysis::render::typed_tsv;
use borer_engine::analysis::utypes::TypeExpr;
use borer_engine::analysis::{Analysis, EnumSource, Overlay, sdk, typelib};
use borer_engine::headers::{ImportName, ImportOrigins, OrdinalName};
use borer_engine::hexdump::hex_rows;
use borer_engine::program::{Arch, BinaryFormat, Program, Symbol, SymbolKind};
use borer_engine::view::Ref;

/// Where every image here enters.
const ENTRY: u64 = 0x40_1000;

/// The global [`reader`] reads, the first byte of `.rdata`.
const GLOBAL: u64 = 0x40_2000;

/// Returns an overlay that reads enums from the binary, as a load makes one.
fn overlay() -> Overlay {
    Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    }
}

/// Builds an x64 image whose entry reads the 32-bit global at [`GLOBAL`],
/// which holds the bytes 1 to 32.
fn reader() -> (Program, Analysis) {
    let code: &[u8] = &[0x8b, 0x05, 0xfa, 0x0f, 0, 0, 0xc3]; // ASM: mov eax,[rip+0xffa]; ret
    let data: Vec<u8> = (1..=32).collect();
    let p = crate::raw::image(Arch::X86_64, code, &data);
    let a = Analysis::compute(&p);
    (p, a)
}

/// A function peeks as the first lines of its decompile view and the count
/// of all of them; a long one says how many it leaves out, and a line is
/// cut at the width cap.
#[test]
fn a_function_peeks_as_its_head_and_its_line_count() {
    let mut code = Vec::new();
    for n in 0..40u8 {
        code.extend([0xc7, 0x05, 0, 0, 0, 0, n, 0, 0, 0]); // ASM: mov dword [rip+0],n
    }
    code.push(0xc3); // ASM: ret
    let p = crate::raw::image(Arch::X86_64, &code, &[]);
    let (a, o) = (Analysis::compute(&p), overlay());
    let v = view(&p, &a, &o, ENTRY).expect("a view");
    let Some(Peek::Function(head)) = peek(&p, &a, &o, &Ref::Function(ENTRY)) else {
        panic!("a function peek");
    };
    assert_eq!(head.total, v.lines());
    assert!(head.total > PEEK_LINES, "{}", v.spell());
    assert_eq!(head.lines.len(), PEEK_LINES);
    assert_eq!(head.more(), v.lines() - PEEK_LINES);
    let first: Vec<_> = (0..PEEK_LINES).filter_map(|i| v.line(i)).collect();
    assert_eq!(head.lines, first);
    let none = peek(&p, &a, &o, &Ref::Function(ENTRY + 1));
    let why = format!("No function starts at {:#x}.", ENTRY + 1);
    assert_eq!(none, Some(Peek::Unknown(why)));
    let long = "x".repeat(PEEK_WIDTH + 5);
    let mut named = overlay();
    named.names.insert(ENTRY, long.clone());
    let Some(Peek::Function(head)) = peek(&p, &a, &named, &Ref::Function(ENTRY)) else {
        panic!("a function peek");
    };
    let wide: Vec<_> = head
        .lines
        .iter()
        .filter(|l| l.contains(&long[..8]))
        .collect();
    assert!(!wide.is_empty(), "{head:?}");
    for line in wide {
        assert_eq!(line.chars().count(), PEEK_WIDTH + 1, "{line}");
        assert!(line.ends_with('…') && !line.contains(&long), "{line}");
    }
}

/// A global with a type applied peeks as the engine's read of the type
/// over its bytes; an untyped one as the hexdump of its first bytes.
#[test]
fn a_global_peeks_as_its_type_or_its_bytes() {
    let (p, a) = reader();
    let ty = TypeExpr::Array(Box::new(TypeExpr::U32), 4);
    let mut typed = overlay();
    typed.applied.extend([(GLOBAL, ty.clone())]);
    let read = typed_tsv(&p, Some(&a), &typed, GLOBAL, &ty).expect("a read");
    let want = read.lines().map(str::to_owned).collect::<Vec<_>>();
    let got = peek(&p, &a, &typed, &Ref::Global(GLOBAL));
    let head = Head {
        total: want.len(),
        lines: want,
    };
    assert_eq!(got, Some(Peek::Global(Read::Typed, head)));
    let row = hex_rows(&p, GLOBAL, PEEK_BYTES).spell(&p).expect("bytes");
    let want = row.lines().map(str::to_owned).collect::<Vec<_>>();
    let got = peek(&p, &a, &overlay(), &Ref::Global(GLOBAL));
    let head = Head {
        total: want.len(),
        lines: want,
    };
    assert_eq!(got, Some(Peek::Global(Read::Bytes, head)));
    let unmapped = peek(&p, &a, &overlay(), &Ref::Global(0x50_0000));
    assert!(matches!(unmapped, Some(Peek::Unknown(_))), "{unmapped:?}");
}

/// An import the file names peeks as its declaration, resolved; one whose
/// name a table lends its ordinal as its declaration, inferred; a slot two
/// imports share as no name and no declaration, unresolved.
#[test]
fn an_import_peeks_as_its_declaration_and_how_sure_its_name_is() {
    let code: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xff, 0x15, 0xf6, 0x0f, 0, 0, // ASM: call [rip+0xff6]
        0xff, 0x15, 0xf8, 0x0f, 0, 0, // ASM: call [rip+0xff8]
        0xff, 0x15, 0xfa, 0x0f, 0, 0, // ASM: call [rip+0xffa]
        0x48, 0x83, 0xc4, 0x28, 0xc3, // ASM: add rsp,0x28; ret
    ];
    let slots = [0x40_2000, 0x40_2008, 0x40_2010];
    let mut p = crate::raw::image(Arch::X86_64, code, &[]);
    p.format = BinaryFormat::Pe;
    let names = [
        ("KERNEL32.dll!Sleep", slots[0]),
        ("KERNEL32.dll!Beep", slots[1]),
        ("KERNEL32.dll!GetTickCount", slots[2]),
        ("KERNEL32.dll!(unnamed)", slots[2]),
    ];
    p.symbols = names
        .map(|(name, addr)| Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Import,
        })
        .to_vec();
    p.headers.import_names = ImportOrigins::new(vec![ImportName {
        slot: slots[1],
        symbol: 1,
        ordinal: Some(5),
        origin: Some(OrdinalName::Listed),
        module: None,
    }]);
    let (a, o) = (Analysis::compute(&p), overlay());
    let decl = |name| {
        let spelled = sdk::spell(typelib::declared(name, BinaryFormat::Pe).expect("declared"));
        Some(Head {
            total: spelled.lines().count(),
            lines: spelled.lines().map(str::to_owned).collect(),
        })
    };
    let want = [
        (Some("Sleep"), Certainty::Resolved, decl("Sleep")),
        (Some("Beep"), Certainty::Inferred, decl("Beep")),
        (None, Certainty::Unresolved, None),
    ];
    for (slot, (name, certainty, decl)) in slots.into_iter().zip(want) {
        let got = peek(&p, &a, &o, &Ref::Import(slot));
        let name = name.map(str::to_owned);
        let want = Peek::Import {
            name,
            certainty,
            decl,
        };
        assert_eq!(got, Some(want), "{slot:#x}");
    }
}

/// A referent a peek never shows answers `None`, apart from one the
/// engine knows nothing of, which answers why.
#[test]
fn a_label_or_a_string_never_peeks() {
    let (p, a) = reader();
    let o = overlay();
    for r in [
        Ref::Address(ENTRY),
        Ref::String(GLOBAL),
        Ref::Comment(ENTRY),
    ] {
        assert_eq!(peek(&p, &a, &o, &r), None, "{r:?}");
    }
}
