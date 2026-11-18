//! One find over every name table: the kinds it answers, how it ranks and
//! scopes them, and that every hit is what the program holds.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeSet;

use borer_engine::analysis::find::{
    CommentKind, Found, Hit, HitKind, KIND_MAX, NEEDLE_MAX, Query, Rank, Source, TEXT_MAX,
    TypeOrigin, everywhere,
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

/// A hundred thousand strings that match exactly are counted whole and
/// kept to one kind's share, and a name that matches only at a word start
/// still makes the list.
#[test]
fn one_huge_table_is_capped_and_starves_no_other() {
    let p = Program::raw(
        b"crypt\0".repeat(100_000),
        Arch::X86_64,
        0,
        None,
        Vec::new(),
    );
    let a = Analysis::default();
    let mut o = Overlay::default();
    o.names.insert(0x10, "my_crypt".to_owned());
    let found = everywhere(&p, &a, &o, &Query::parse("crypt"), 3 * KIND_MAX);
    assert_eq!(
        found.counted,
        [(HitKind::String, 100_000), (HitKind::Name, 1)]
    );
    let strings = found
        .hits
        .iter()
        .filter(|h| h.kind() == HitKind::String)
        .count();
    assert_eq!(strings, KIND_MAX);
    let name = one(&found, HitKind::Name);
    assert_eq!((&*name.text, name.rank), ("my_crypt", Rank::Word));
}

/// A megabyte of query, a query of combining marks, an empty query and
/// address forms past every place each answer within the limit and the
/// kind cap, and the empty query finds nothing.
#[test]
fn a_hostile_query_answers_within_the_caps() {
    let (p, o) = fixture();
    let a = Analysis::compute(&p);
    let long = "a".repeat(1 << 20);
    let marks = "\u{301}".repeat(1 << 18);
    for text in [
        long.as_str(),
        marks.as_str(),
        "",
        "@",
        "t:",
        "\"",
        "#",
        "0x",
        "rva:0xffffffffffffffff",
        "off:0xffffffffffffffff",
        "18446744073709551615",
    ] {
        let found = everywhere(&p, &a, &o, &Query::parse(text), 10);
        assert!(found.hits.len() <= 10, "{found:?}");
        for (kind, _) in &found.counted {
            let kept = found.hits.iter().filter(|h| h.kind() == *kind).count();
            assert!(kept <= KIND_MAX, "{found:?}");
        }
    }
    assert_eq!(
        everywhere(&p, &a, &o, &Query::parse(""), 10),
        Found::default()
    );
}

/// A find spells a header counting each kind and one row per hit with its
/// rank, kind, address, source and text.
#[test]
fn a_find_spells_one_row_per_hit() {
    let text = find("crypt").spell();
    assert!(
        text.starts_with("# showing 9 of 9 hits: function 1 of 1, import 1 of 1, ")
            && text.contains("\n# rank kind addr source text\n"),
        "{text}"
    );
    for row in [
        "prefix function 0x401000 sym crypt_init\n",
        "prefix import 0x402100 import:ADVAPI32.dll CryptEncrypt\n",
        "prefix string 0x402000 .rdata:ascii crypto\n",
        "prefix type - usr crypt_ctx\n",
        "word comment 0x401000 question ?crypt key\n",
    ] {
        assert!(text.contains(row), "{row}: {text}");
    }
    let entry = find("0x401000").spell();
    assert!(
        entry.contains("\nexact address 0x401000 va crypt_init\n"),
        "{entry}"
    );
}

/// A needle cut to its cap matches no text whole and the header says it
/// was cut, and a hit's text past its cap ends in `...`.
#[test]
fn a_cut_needle_and_a_cut_text_say_so() {
    let whole = "a".repeat(NEEDLE_MAX);
    let mut bytes = format!("{whole}\0").into_bytes();
    bytes.extend_from_slice(format!("{}\0", "b".repeat(300)).as_bytes());
    let p = Program::raw(bytes, Arch::X86_64, 0, None, Vec::new());
    let (a, o) = (Analysis::default(), Overlay::default());
    let cut = Query::parse(&format!("{whole}{}", "x".repeat(44)));
    assert!(cut.cut);
    let found = everywhere(&p, &a, &o, &cut, 100);
    assert_eq!(
        found.hits.iter().map(|h| h.rank).collect::<Vec<_>>(),
        [Rank::Prefix]
    );
    assert!(
        found
            .spell()
            .starts_with("# showing 1 of 1 hits: string 1 of 1; needle cut to 256 characters; 1 text cut to 200 characters\n"),
        "{found:?}"
    );
    let long = everywhere(&p, &a, &o, &Query::parse("bbb"), 100);
    let hit = one(&long, HitKind::String);
    assert_eq!(&*hit.text, format!("{}...", "b".repeat(TEXT_MAX)));
    assert!(hit.cut);
}

/// A place no section maps says so in the header instead of heading the
/// list.
#[test]
fn an_unmapped_address_says_so() {
    let text = find("rva:0x90000").spell();
    assert!(
        text.starts_with("# showing 0 of 0 hits; the address is in no mapped section\n"),
        "{text}"
    );
    let off = find("off:0x900000").spell();
    assert!(
        off.starts_with("# showing 0 of 0 hits; the file offset is in no mapped section\n"),
        "{off}"
    );
    assert!(!find("rva:0x1000").spell().contains("no mapped section"));
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

/// A section name with a blank stays one column of a spelled row.
#[test]
fn a_blank_in_a_section_name_stays_one_column() {
    let mut bytes = b"crypto\0".to_vec();
    bytes.resize(0x10, 0);
    let section = Section::mapped("my sec", 0x1000, 0, 0x10, false, false);
    let p = Program::raw(bytes, Arch::X86_64, 0, None, vec![section]);
    let found = everywhere(
        &p,
        &Analysis::default(),
        &Overlay::default(),
        &Query::parse("crypt"),
        100,
    );
    let text = found.spell();
    assert!(
        text.contains("\nprefix string 0x1000 my\\x20sec:ascii crypto\n"),
        "{text}"
    );
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

/// An address in a `.bss` is a place by name wherever one is asked for: a
/// find hit, the signature and YARA refusals, and the RVA a number is
/// read as when no function holds it.
///
/// The YARA rule is asked of an image whose function's section lost its
/// file bytes, the one way a function's entry has none.
#[test]
fn a_bss_address_is_named_by_find_signature_and_function_answers() {
    use borer_engine::analysis::no_function_at;
    use borer_engine::analysis::render::{signature, yara_rule};
    let text = || Section::mapped(".text", 0x40_1000, 0, 0x10, false, true);
    let bss = |name: &str, va: u64| {
        let mut bss = Section::mapped(name, va, 0, 0x1000, true, false);
        bss.file_size = 0;
        bss
    };
    let image = |sections| Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0x40_0000, None, sections);
    let p = image(vec![text(), bss(".bss", 0x40_2000)]);
    let (a, o) = (Analysis::compute(&p), Overlay::default());
    let found = everywhere(&p, &a, &o, &Query::parse("0x402010"), 100);
    let first = found.hits.first().map(|h| (h.kind(), h.addr, &*h.text));
    assert_eq!(first, Some((HitKind::Address, Some(0x40_2010), ".bss")));
    assert_eq!(
        signature(&p, 0x40_2010, None).err().as_deref(),
        Some("address 0x402010 is in .bss, which holds no file bytes (the loader zero-fills it)")
    );
    assert_eq!(
        no_function_at(&p, &a, 0x2010),
        "no discovered function contains 0x2010: it is outside the image (0x401000..0x403000); as an RVA it is 0x402010, which is mapped"
    );
    let at = |section| {
        Program::raw(
            vec![0xc3; 0x10],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![section],
        )
    };
    let functions = Analysis::compute(&at(Section::mapped(".text", 0x1000, 0, 0x10, false, true)));
    assert!(functions.function_at(0x1000).is_some());
    let why = yara_rule(&at(bss(".bss", 0x1000)), &functions, &o, &[0x1000])
        .expect_err("no bytes to match");
    assert!(
        why.ends_with(
            ": address 0x1000 is in .bss, which holds no file bytes (the loader zero-fills it)"
        ),
        "{why}"
    );
}
