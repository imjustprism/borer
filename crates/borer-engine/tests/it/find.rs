//! One find over every name table: the kinds it answers, how it ranks and
//! scopes them, and that every hit is what the program holds.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeSet;

use borer_engine::analysis::find::{
    CommentKind, Found, Hit, HitKind, KIND_MAX, Query, Rank, Source, TypeOrigin, everywhere,
};
use borer_engine::analysis::render::RowSource;
use borer_engine::analysis::utypes::{TypeExpr, UserType};
use borer_engine::analysis::{Analysis, NameSource, Overlay};
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
use borer_engine::strings::Encoding;

/// Where the one function starts, the image's entry.
const ENTRY: u64 = 0x40_1000;

/// Builds the image every test searches, with its overlay.
///
/// It holds a function `crypt_init` at the entry, an import `CryptEncrypt`,
/// the strings `crypto` and UTF-16 `CryptWide`, two named data `crypt_key`
/// listed out of address order, a user type `crypt_ctx` and an open
/// question `?crypt key` at the entry.
fn fixture() -> (Program, Overlay) {
    let code = [0xc3]; // ASM: ret
    let mut data = b"crypto\0".to_vec();
    data.resize(0x40, 0);
    for unit in "CryptWide".encode_utf16() {
        data.extend_from_slice(&unit.to_le_bytes());
    }
    let mut p = crate::raw::image(Arch::X86_64, &code, &data);
    let symbol = |name: &str, addr: u64, kind: SymbolKind| Symbol {
        name: name.to_owned(),
        addr,
        kind,
    };
    p.symbols = vec![
        symbol("crypt_init", ENTRY, SymbolKind::Export),
        symbol("ADVAPI32.dll!CryptEncrypt", 0x40_2100, SymbolKind::Import),
        symbol("crypt_key", 0x40_2200, SymbolKind::Data),
        symbol("crypt_key", 0x40_2180, SymbolKind::Data),
    ];
    let mut o = Overlay::default();
    o.types
        .insert("crypt_ctx".to_owned(), UserType::Alias(TypeExpr::U32));
    o.comments.insert(ENTRY, "?crypt key".to_owned());
    (p, o)
}

/// Finds `text` in the fixture with room for every hit.
///
/// # Arguments
///
/// * `text` - The query as typed.
fn find(text: &str) -> Found {
    let (p, o) = fixture();
    let a = Analysis::compute(&p);
    everywhere(&p, &a, &o, &Query::parse(text), 1000)
}

/// Returns the kinds a find answered.
///
/// # Arguments
///
/// * `found` - The find.
fn kinds(found: &Found) -> BTreeSet<HitKind> {
    found.hits.iter().map(Hit::kind).collect()
}

/// Returns the one hit of `kind`.
///
/// # Arguments
///
/// * `found` - The find.
/// * `kind` - The kind sought.
#[expect(
    clippy::panic,
    reason = "a test helper; the panic names the missing kind and the find"
)]
fn one(found: &Found, kind: HitKind) -> &Hit {
    let mut of = found.hits.iter().filter(|h| h.kind() == kind);
    let hit = of
        .next()
        .unwrap_or_else(|| panic!("no {kind:?} in {found:?}"));
    assert!(of.next().is_none(), "two {kind:?} in {found:?}");
    hit
}

/// Asserts the hits are in the order the find promises: rank, kind, those
/// with an address first, address, text.
///
/// # Arguments
///
/// * `found` - The find.
fn assert_ordered(found: &Found) {
    let key = |h: &Hit| (h.rank, h.kind(), h.addr.is_none(), h.addr, h.text.clone());
    assert!(
        found.hits.windows(2).all(|w| key(&w[0]) <= key(&w[1])),
        "{found:?}"
    );
}

/// One query answers a function, an import, a string, a user type and a
/// comment, each with how borer knows it, the prefix hits before the
/// word-start ones.
#[test]
fn one_query_answers_every_table() {
    let found = find("crypt");
    for kind in [
        HitKind::Function,
        HitKind::Import,
        HitKind::Export,
        HitKind::Symbol,
        HitKind::String,
        HitKind::Type,
        HitKind::Comment,
    ] {
        assert!(kinds(&found).contains(&kind), "no {kind:?} in {found:?}");
    }
    assert_ordered(&found);
    let function = one(&found, HitKind::Function);
    assert_eq!(
        (
            function.addr,
            &*function.text,
            &function.source,
            function.rank
        ),
        (
            Some(ENTRY),
            "crypt_init",
            &Source::Function(RowSource::Found(NameSource::Symbol)),
            Rank::Prefix
        )
    );
    let import = one(&found, HitKind::Import);
    assert_eq!(
        (&*import.text, &import.source, import.rank),
        (
            "CryptEncrypt",
            &Source::Symbol {
                kind: SymbolKind::Import,
                module: Some("ADVAPI32.dll".into())
            },
            Rank::Prefix
        )
    );
    let strings: Vec<(&str, &Source)> = found
        .hits
        .iter()
        .filter(|h| h.kind() == HitKind::String)
        .map(|h| (&*h.text, &h.source))
        .collect();
    assert_eq!(
        strings,
        [
            (
                "crypto",
                &Source::String {
                    off: 0x1000,
                    section: Some(".rdata".into()),
                    encoding: Encoding::Ascii
                }
            ),
            (
                "CryptWide",
                &Source::String {
                    off: 0x1040,
                    section: Some(".rdata".into()),
                    encoding: Encoding::Utf16
                }
            )
        ]
    );
    let ty = one(&found, HitKind::Type);
    assert_eq!(
        (&*ty.text, &ty.source),
        ("crypt_ctx", &Source::Type(TypeOrigin::User))
    );
    let comment = one(&found, HitKind::Comment);
    assert_eq!(
        (comment.addr, &comment.source, comment.rank),
        (
            Some(ENTRY),
            &Source::Comment(CommentKind::Question),
            Rank::Word
        )
    );
    assert_eq!(found.hits.first().map(|h| h.rank), Some(Rank::Prefix));
    assert_eq!(found.hits.last().map(Hit::kind), Some(HitKind::Comment));
}

/// A kind prefix narrows the tables, and an address form is answered
/// first, as the function holding it or the section.
#[test]
fn a_prefix_narrows_and_an_address_comes_first() {
    let only = |text: &str, kind: HitKind| {
        let found = find(text);
        assert_eq!(kinds(&found), BTreeSet::from([kind]), "{text}: {found:?}");
    };
    only("@crypt", HitKind::Function);
    only("\"cry", HitKind::String);
    only("t:crypt", HitKind::Type);
    only("#crypt", HitKind::Comment);
    let entry = find(&format!("{ENTRY:#x}"));
    let first = entry.hits.first().map(|h| (h.kind(), h.addr, &*h.text));
    assert_eq!(
        first,
        Some((HitKind::Address, Some(ENTRY), "crypt_init")),
        "{entry:?}"
    );
    let rdata = find("rva:0x2000");
    let first = rdata.hits.first().map(|h| (h.kind(), h.addr, &*h.text));
    assert_eq!(
        first,
        Some((HitKind::Address, Some(0x40_2000), ".rdata")),
        "{rdata:?}"
    );
    assert!(find("rva:0x90000").hits.is_empty());
}

/// The same query gives the same hits twice, on a clone of the analysis
/// and on one computed again, and two hits of one rank, kind and text are
/// listed by address whatever order their table holds them in.
#[test]
#[expect(
    clippy::redundant_clone,
    reason = "the clone carries the memo the first finds built"
)]
fn a_find_is_deterministic() {
    let (p, o) = fixture();
    let a = Analysis::compute(&p);
    let q = Query::parse("crypt");
    let first = everywhere(&p, &a, &o, &q, 1000);
    assert_eq!(first, everywhere(&p, &a, &o, &q, 1000));
    assert_eq!(first, everywhere(&p, &a.clone(), &o, &q, 1000));
    assert_eq!(first, everywhere(&p, &Analysis::compute(&p), &o, &q, 1000));
    let keys: Vec<Option<u64>> = first
        .hits
        .iter()
        .filter(|h| h.kind() == HitKind::Symbol)
        .map(|h| h.addr)
        .collect();
    assert_eq!(keys, [Some(0x40_2180), Some(0x40_2200)]);
    assert_ordered(&first);
}

/// Every function hit is a discovered entry, and every string hit's bytes
/// spell its text where it says it lies.
#[test]
fn every_hit_is_what_the_program_holds() {
    let (p, o) = fixture();
    let a = Analysis::compute(&p);
    let found = everywhere(&p, &a, &o, &Query::parse("cr"), 1000);
    assert!(!found.hits.is_empty());
    for hit in &found.hits {
        match (hit.kind(), &hit.source) {
            (HitKind::Function, _) => {
                assert!(hit.addr.is_some_and(|e| a.function(e).is_some()), "{hit:?}");
            }
            (HitKind::String, Source::String { off, encoding, .. }) => {
                let va = hit.addr.unwrap_or_else(|| panic!("{hit:?}"));
                assert_eq!(p.va_to_offset(va), Some(*off), "{hit:?}");
                let spelled: Vec<u8> = match encoding {
                    Encoding::Ascii => hit.text.bytes().collect(),
                    Encoding::Utf16 | Encoding::DotnetUs => {
                        hit.text.encode_utf16().flat_map(u16::to_le_bytes).collect()
                    }
                };
                assert_eq!(
                    p.read_va_upto(va, spelled.len()),
                    Some(spelled.as_slice()),
                    "{hit:?}"
                );
            }
            (HitKind::String, _) => panic!("a string hit not from the walk: {hit:?}"),
            _ => {}
        }
    }
}

/// `thunk` is a word like any other, and a thunk is a function a query
/// finds by its name.
#[test]
fn a_thunk_is_a_function_by_its_name() {
    let mut code = vec![0xcc; 0x16];
    code[..6].copy_from_slice(&[0xe8, 0x0b, 0x00, 0x00, 0x00, 0xc3]); // ASM: call 0x401010; ret
    code[0x10..].copy_from_slice(&[0xff, 0x25, 0xea, 0x10, 0x00, 0x00]); // ASM: jmp [rip + 0x10ea]
    let mut p = crate::raw::image(Arch::X86_64, &code, &[]);
    p.symbols = vec![
        Symbol {
            name: "thunk_helper".to_owned(),
            addr: ENTRY,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "KERNEL32.dll!Sleep".to_owned(),
            addr: 0x40_2100,
            kind: SymbolKind::Import,
        },
    ];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let at = |text: &str| -> Vec<Option<u64>> {
        everywhere(&p, &a, &o, &Query::parse(text), 100)
            .hits
            .iter()
            .map(|h| h.addr)
            .collect()
    };
    assert_eq!(at("@thunk"), [Some(ENTRY)]);
    assert_eq!(at("@sleep"), [Some(0x40_1010)]);
}

/// Under `#` a user's name at a function's entry is a name hit; a search
/// of every table lists it as the function's.
#[test]
fn a_name_at_an_entry_is_found_under_notes() {
    let (p, mut o) = fixture();
    o.names.insert(ENTRY, "crypt_entry".to_owned());
    let a = Analysis::compute(&p);
    let notes = everywhere(&p, &a, &o, &Query::parse("#crypt_entry"), 100);
    let name = one(&notes, HitKind::Name);
    assert_eq!((name.addr, &name.source), (Some(ENTRY), &Source::User));
    let all = everywhere(&p, &a, &o, &Query::parse("crypt_entry"), 100);
    assert!(!kinds(&all).contains(&HitKind::Name), "{all:?}");
    let function = one(&all, HitKind::Function);
    assert_eq!(function.source, Source::Function(RowSource::User));
}

/// Imports with no slot do not push a mapped one out of a kind's share.
#[test]
fn an_unbound_import_yields_to_a_mapped_one() {
    let mut p = crate::raw::image(Arch::X86_64, &[0xc3], &[]); // ASM: ret
    p.symbols = (0..60)
        .map(|k| Symbol {
            name: format!("KERNEL32.dll!crypt_{k:02}"),
            addr: 0,
            kind: SymbolKind::Import,
        })
        .chain([Symbol {
            name: "KERNEL32.dll!crypt_zz".to_owned(),
            addr: 0x40_2100,
            kind: SymbolKind::Import,
        }])
        .collect();
    let a = Analysis::compute(&p);
    let found = everywhere(&p, &a, &Overlay::default(), &Query::parse("crypt"), 1000);
    assert_eq!(found.counted, [(HitKind::Import, 61)]);
    assert_eq!(found.hits.len(), KIND_MAX);
    assert_eq!(found.hits.first().map(|h| h.addr), Some(Some(0x40_2100)));
}

/// A relative address with a hex letter and no `0x` names the place a find
/// and `borer://addr` agree on.
#[test]
fn a_find_and_addr_read_a_place_alike() {
    let (p, o) = fixture();
    let a = Analysis::compute(&p);
    let located = borer_engine::fileinfo::locate(&p, Some(&a), &o, "rva:1a00").expect("a place");
    assert!(located.starts_with("va:       0x401a00\n"), "{located}");
    let found = everywhere(&p, &a, &o, &Query::parse("rva:1a00"), 100);
    let first = found.hits.first().map(|h| (h.kind(), h.addr, &*h.text));
    assert_eq!(first, Some((HitKind::Address, Some(0x40_1a00), ".text")));
}

/// A word that also spells hex is a word: `add` finds the function
/// `add_one`, not the place `0xadd`.
#[test]
fn a_word_that_spells_hex_is_no_address() {
    let mut code = vec![0xcc; 0x1000];
    code[0] = 0xc3; // ASM: ret
    let section = Section::mapped(".text", 0x100, 0, 0x1000, false, true);
    let mut p = Program::raw(code, Arch::X86_64, 0, Some(0x100), vec![section]);
    p.symbols = vec![Symbol {
        name: "add_one".to_owned(),
        addr: 0x100,
        kind: SymbolKind::Export,
    }];
    let a = Analysis::compute(&p);
    let found = everywhere(&p, &a, &Overlay::default(), &Query::parse("add"), 100);
    assert!(!kinds(&found).contains(&HitKind::Address), "{found:?}");
    let first = found.hits.first().map(|h| (h.kind(), h.addr, &*h.text));
    assert_eq!(first, Some((HitKind::Function, Some(0x100), "add_one")));
}

/// A number a user name spells is the name's hit, not an address.
#[test]
fn a_name_that_spells_a_number_is_a_name() {
    let (p, mut o) = fixture();
    o.names.insert(ENTRY, "1234".to_owned());
    let a = Analysis::compute(&p);
    let found = everywhere(&p, &a, &o, &Query::parse("1234"), 100);
    assert!(!kinds(&found).contains(&HitKind::Address), "{found:?}");
    let function = one(&found, HitKind::Function);
    assert_eq!(
        (function.addr, &*function.text, function.rank),
        (Some(ENTRY), "1234", Rank::Exact)
    );
}

/// An import's whole name, module included, matches it exactly, and its
/// start ranks prefix.
#[test]
fn a_whole_import_name_is_exact() {
    let mut p = crate::raw::image(Arch::X86_64, &[0xc3], &[]); // ASM: ret
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!Sleep".to_owned(),
        addr: 0x40_2100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let rank = |text: &str| {
        one(
            &everywhere(&p, &a, &o, &Query::parse(text), 100),
            HitKind::Import,
        )
        .rank
    };
    assert_eq!(rank("kernel32.dll!sleep"), Rank::Exact);
    assert_eq!(rank("sleep"), Rank::Exact);
    assert_eq!(rank("kernel32"), Rank::Prefix);
    assert_eq!(rank("32.dll"), Rank::Substring);
}
