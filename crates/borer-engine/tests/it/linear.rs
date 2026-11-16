//! The linear listing: the whole image in address order, paged by address
//! in both directions, every line answering its address.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{Dir, LINES_MAX, LinearPage, RowKind, linear};
use borer_engine::analysis::utypes::TypeExpr;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::dwarf::Global;
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
use borer_engine::view::{Kind, Ref};

/// The image base of the fixture.
const BASE: u64 = 0x1_4000_0000;
/// The code section's base.
const TEXT: u64 = 0x1_4000_1000;
/// The helper function's entry.
const HELPER: u64 = 0x1_4000_1040;
/// The read-only data section's base.
const RDATA: u64 = 0x1_4000_2000;
/// Where the read-only data section ends and the unmapped gap starts.
const GAP: u64 = 0x1_4000_2100;
/// The writable data section's base.
const DATA: u64 = 0x1_4000_3000;
/// Where the writable data section's file bytes end.
const ZERO: u64 = 0x1_4000_3100;
/// One past the image's last address.
const END: u64 = 0x1_4000_3200;

/// Builds an x64 image with code, a string, a pointer table, an unmapped
/// gap and a zero-filled tail.
///
/// `.text` holds `call helper; ret` at its start and `helper: ret`, int3
/// around them; `.rdata` a string and a table of the two functions' entries;
/// `.data` maps twice the bytes the file holds.
fn image() -> Program {
    let mut bytes = vec![0u8; 0x300];
    bytes[..0x100].fill(0xcc);
    let main: &[u8] = &[
        // ASM: call 0x140001040
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: ret
        0xc3,
    ];
    bytes[..main.len()].copy_from_slice(main);
    // ASM: ret
    bytes[0x40] = 0xc3;
    bytes[0x100..0x114].copy_from_slice(b"hello, linear world\0");
    bytes[0x120..0x128].copy_from_slice(&TEXT.to_le_bytes());
    bytes[0x128..0x130].copy_from_slice(&HELPER.to_le_bytes());
    let mut data = Section::mapped(".data", DATA, 0x200, 0x100, true, false);
    data.vsize = 0x200;
    let sections = vec![
        Section::mapped(".text", TEXT, 0, 0x100, false, true),
        Section::mapped(".rdata", RDATA, 0x100, 0x100, false, false),
        data,
    ];
    let mut p = Program::raw(bytes, Arch::X86_64, BASE, Some(TEXT), sections);
    p.format = BinaryFormat::Pe;
    p
}

/// Returns the addresses of a page's rows, in order.
///
/// It first checks that every line with text answers an address, that the lines' addresses are
/// the rows' and that each row's span ends where the next one starts.
///
/// # Arguments
///
/// * `page` - The page.
fn rows(page: &LinearPage) -> Vec<u64> {
    let v = &page.view;
    let mut out: Vec<u64> = Vec::new();
    for i in 0..v.lines() {
        if v.line(i).is_none_or(str::is_empty) {
            continue;
        }
        let va = v.address(i).expect("every line answers its address");
        if out.last() != Some(&va) {
            out.push(va);
        }
    }
    let starts: Vec<u64> = page.rows.iter().map(|r| r.span.start).collect();
    assert_eq!(out, starts, "the lines' rows are the page's rows");
    assert!(
        page.rows
            .windows(2)
            .all(|w| w[0].span.end == w[1].span.start)
    );
    assert_eq!(
        page.rows.last().map(|r| r.span.end),
        page.next.or_else(|| page.rows.last().map(|r| r.span.end))
    );
    out
}

/// Returns the line of a page that starts with `prefix`.
///
/// # Arguments
///
/// * `page` - The page.
/// * `prefix` - The line's start.
fn line<'a>(page: &'a LinearPage, prefix: &str) -> Option<&'a str> {
    let v = &page.view;
    (0..v.lines())
        .filter_map(|i| v.line(i))
        .find(|l| l.starts_with(prefix))
}

/// Returns the pages of the image from its start, each `n` rows, chained by
/// `next`.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
/// * `n` - Rows per page.
fn chain(p: &Program, a: &Analysis, n: usize) -> Vec<LinearPage> {
    let o = Overlay::default();
    let mut pages: Vec<LinearPage> = Vec::new();
    let mut at = Some(0);
    while let Some(va) = at {
        let page = linear(p, a, &o, va, Dir::Next, n).expect("a page");
        at = page.next;
        pages.push(page);
        assert!(pages.len() < 10_000, "the chain ends");
    }
    pages
}

/// Chained pages cover the image once, in address order.
///
/// Pages chained from the image's start reach its end with no address
/// skipped or shown twice: each page starts where the one before said the
/// next starts, the rows run in address order without repeating, every
/// section, the gap and the zero-filled tail start a row, and every
/// instruction has its row.
#[test]
fn chained_pages_cover_the_image_once_in_address_order() {
    let p = image();
    let a = Analysis::compute(&p);
    let pages = chain(&p, &a, 5);
    assert_eq!(pages.first().map(|pg| pg.first), Some(TEXT));
    assert!(pages.last().is_some_and(|pg| pg.next.is_none()));
    let mut all: Vec<u64> = Vec::new();
    for (k, page) in pages.iter().enumerate() {
        if k > 0 {
            assert_eq!(
                pages[k - 1].next,
                Some(page.first),
                "page {k} starts at its next"
            );
        }
        let shown = rows(page);
        assert_eq!(
            shown.first(),
            Some(&page.first),
            "page {k} starts at its first row"
        );
        assert!(shown.len() == 5 || page.next.is_none(), "page {k} is full");
        all.extend(shown);
    }
    assert!(all.windows(2).all(|w| w[0] < w[1]), "rows repeat: {all:x?}");
    assert!(all.iter().all(|&va| (TEXT..END).contains(&va)));
    for start in [TEXT, TEXT + 5, HELPER, RDATA, GAP, DATA, ZERO] {
        assert!(all.contains(&start), "{start:#x} starts no row: {all:x?}");
    }
    let gap = pages
        .iter()
        .find_map(|pg| line(pg, "; unmapped"))
        .expect("the gap's line");
    assert_eq!(
        gap,
        "; unmapped 0x140001100..0x140002000 (0xf00 bytes): no section maps it"
    );
    let tail = pages
        .iter()
        .find_map(|pg| line(pg, "; zero-filled"))
        .expect("the tail's line");
    assert_eq!(
        tail,
        "; zero-filled 0x140003100..0x140003200 (0x100 bytes): the file holds no bytes for it"
    );
}

/// The page before page N, asked at page N's start, is page N-1 line for
/// line, and page N's `prev` names where it starts.
#[test]
fn the_page_before_a_page_is_the_one_whose_next_it_is() {
    let p = image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for n in [1, 3, 5, 8] {
        let pages = chain(&p, &a, n);
        assert!(pages.len() > 2, "{n} rows a page make several pages");
        assert_eq!(pages[0].prev, None);
        for k in 1..pages.len() {
            let back = linear(&p, &a, &o, pages[k].first, Dir::Prev, n).expect("a page");
            assert_eq!(
                pages[k].prev,
                Some(pages[k - 1].first),
                "{n} rows, page {k}"
            );
            assert_eq!(back.first, pages[k - 1].first, "{n} rows, page {k}");
            assert_eq!(
                back.view.spell(),
                pages[k - 1].view.spell(),
                "{n} rows, page {k}"
            );
        }
    }
}

/// A page asked at an address inside an instruction starts at that
/// instruction, under its section's and its function's headers.
#[test]
fn a_page_inside_an_instruction_starts_at_it() {
    let p = image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let page = linear(&p, &a, &o, TEXT + 2, Dir::Next, 3).expect("a page");
    assert_eq!(page.first, TEXT);
    assert_eq!(rows(&page).first(), Some(&TEXT));
    assert!(
        line(&page, "; section .text r-x 0x140001000..0x140001100").is_some(),
        "{}",
        page.view.spell()
    );
    assert!(line(&page, "; function sub_140001000").is_some());
    assert!(
        line(&page, "0x140001000  call").is_some(),
        "{}",
        page.view.spell()
    );
    assert!(line(&page, "0x140001002").is_none());
}

/// A 64 MiB section no fact covers costs one page of a few lines.
///
/// They are its header, the line saying no reference the engine recorded
/// reaches it, 16 hex rows and one line that skips the rest and says where
/// the range ends.
#[test]
fn an_uncovered_range_is_capped_by_a_skip_line() {
    let size: u64 = 64 << 20;
    let len = usize::try_from(size).expect("fits");
    let p = Program::raw(
        vec![0u8; len],
        Arch::X86_64,
        0,
        None,
        vec![Section::mapped(".data", 0x10000, 0, size, true, false)],
    );
    let a = Analysis::default();
    let o = Overlay::default();
    let page = linear(&p, &a, &o, 0x10000, Dir::Next, LINES_MAX).expect("a page");
    let text: Vec<&str> = (0..page.view.lines())
        .filter_map(|i| page.view.line(i))
        .filter(|l| !l.is_empty())
        .collect();
    assert_eq!(text.len(), 19, "{text:#?}");
    assert_eq!(
        text[1],
        "; unexplored 0x10000..0x4010000 (0x4000000 bytes): no reference the engine recorded reaches it"
    );
    assert_eq!(
        text[2],
        "0x10000  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00"
    );
    assert_eq!(
        text[18],
        "; 0x3ffff00 more bytes not shown; the range ends at 0x4010000"
    );
    assert_eq!(page.next, None);
    assert_eq!(rows(&page).len(), 17);
}

/// Returns the text and link of each linked token of the page's line that
/// starts with `prefix`.
///
/// # Arguments
///
/// * `page` - The page.
/// * `prefix` - The line's start.
fn links(page: &LinearPage, prefix: &str) -> Vec<(String, Kind, Ref)> {
    let v = &page.view;
    let i = (0..v.lines())
        .find(|&i| v.line(i).is_some_and(|l| l.starts_with(prefix)))
        .expect("the line");
    let line = v.line(i).expect("the line");
    v.tokens(i)
        .filter_map(|(span, kind, link)| Some((line[span].to_owned(), kind, link?.clone())))
        .collect()
}

/// Data lines spell their facts and link what they name.
///
/// A string, a table of function pointers, a type the user applied, a
/// debug global and a data symbol each get the line their fact spells,
/// linked to what they name, and the bytes a data symbol names run as hex
/// rows to the next fact.
#[test]
fn data_lines_spell_their_facts_and_link_what_they_name() {
    let mut p = image();
    p.bytes[0x130] = 0x2a;
    p.bytes[0x200] = 0x07;
    p.symbols.push(Symbol {
        name: "g_names".to_owned(),
        addr: RDATA + 0x40,
        kind: SymbolKind::Data,
    });
    p.debug_globals.push(Global {
        name: "g_count".to_owned(),
        addr: Some(DATA),
        type_name: Some("int".to_owned()),
        ty: Some(TypeExpr::I32),
    });
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.applied.insert(RDATA + 0x30, TypeExpr::U32);
    o.applied.insert(RDATA + 1, TypeExpr::U16);
    let page = linear(&p, &a, &o, RDATA, Dir::Next, 64).expect("a page");
    let text = page.view.spell();
    for want in [
        "0x140002000  \"hello, linear world\"  ; ascii 19",
        "0x140002020  ptr 0x140001000  ; -> sub_140001000",
        "0x140002028  ptr 0x140001040  ; -> sub_140001040",
        "0x140002030  u32 = 0x2a  ; a type the user applied",
        "; data g_names 0x140002040..0x140002100 (0xc0 bytes): a name the file states, of no size the engine knows",
        "0x140002040  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00",
        "0x140003000  g_count i32 = 7  ; a type the debug information states",
        "; the type u16 applied at 0x140002001 is not laid out: what this row shows covers it",
    ] {
        assert!(
            text.lines().any(|l| l == want),
            "no line {want:?} in\n{text}"
        );
    }
    assert_eq!(
        links(&page, "0x140002000"),
        vec![(
            "\"hello, linear world\"".to_owned(),
            Kind::String,
            Ref::String(RDATA)
        )]
    );
    assert_eq!(
        links(&page, "0x140002020"),
        vec![
            ("0x140001000".to_owned(), Kind::Address, Ref::Function(TEXT)),
            (
                "sub_140001000".to_owned(),
                Kind::Function,
                Ref::Function(TEXT)
            ),
        ]
    );
    assert!(
        !text.contains("0x140002010  "),
        "the string's bytes have no hex row"
    );
    let kinds: Vec<(u64, RowKind)> = page.rows.iter().map(|r| (r.span.start, r.kind)).collect();
    for want in [
        (RDATA, RowKind::String),
        (RDATA + 0x14, RowKind::Unexplored),
        (RDATA + 0x20, RowKind::Pointer),
        (RDATA + 0x30, RowKind::Value),
        (RDATA + 0x40, RowKind::Named),
        (GAP, RowKind::Unmapped),
    ] {
        assert!(kinds.contains(&want), "no row {want:x?} in {kinds:x?}");
    }
    let string = page.rows.iter().find(|r| r.span.start == RDATA);
    assert_eq!(
        string.map(|r| r.span.end),
        Some(RDATA + 0x14),
        "the NUL is the string's"
    );
}

/// Builds an x64 image of `.text` holding `code` at its start, entered
/// there, followed by `.rdata` holding `data`, at the next address.
///
/// # Arguments
///
/// * `code` - The code section's bytes.
/// * `data` - The data section's bytes, none for an image of code alone.
fn two_sections(code: &[u8], data: &[u8]) -> Program {
    let code_len = u64::try_from(code.len()).expect("fits");
    let data_len = u64::try_from(data.len()).expect("fits");
    let mut sections = vec![Section::mapped(".text", TEXT, 0, code_len, false, true)];
    if !data.is_empty() {
        let va = TEXT + code_len;
        sections.push(Section::mapped(
            ".rdata", va, code_len, data_len, false, false,
        ));
    }
    let mut p = Program::raw(
        [code, data].concat(),
        Arch::X86_64,
        BASE,
        Some(TEXT),
        sections,
    );
    p.format = BinaryFormat::Pe;
    p
}

/// Builds an image whose sections overlap each other, one reaching the end
/// of the address space and one claiming more file than there is: a table
/// no loader passes, built by hand.
fn hostile() -> Program {
    let mut huge = Section::mapped(".huge", 0x2000, 0x100, 0x100, true, false);
    huge.vsize = u64::MAX - 0x2000;
    let mut wide = Section::mapped(".wide", 0x800, 0, 0x200, false, true);
    wide.file_size = 0x400;
    let sections = vec![
        Section::mapped(".a", 0x1000, 0, 0x1000, false, true),
        Section::mapped(".b", 0x1800, 0x80, 0x1000, true, false),
        huge,
        wide,
        Section::mapped(".dup", 0x1000, 0, 0x1000, false, false),
    ];
    Program::raw(vec![0x90; 0x200], Arch::X86_64, 0, Some(0x1000), sections)
}

/// Pages asked anywhere, either way, answer a hostile section table within
/// their caps, without a panic: no page holds more than [`LINES_MAX`] rows
/// and a chain of pages moves forward.
#[test]
fn overlapping_and_huge_sections_page_within_the_caps() {
    let p = hostile();
    let o = Overlay::default();
    for a in [Analysis::default(), Analysis::compute(&p)] {
        for at in [0, 0x1000, 0x17ff, 0x2000, 1 << 40, u64::MAX] {
            for dir in [Dir::Next, Dir::Prev] {
                let page = linear(&p, &a, &o, at, dir, usize::MAX).expect("a page");
                let shown = rows(&page);
                assert!(
                    shown.len() <= LINES_MAX,
                    "{at:#x} {dir:?}: {} rows",
                    shown.len()
                );
                assert!(page.next.is_none_or(|next| next > page.first));
                assert!(page.prev.is_none_or(|prev| prev < page.first));
            }
        }
        let mut at = Some(0);
        for _ in 0..64 {
            let Some(va) = at else {
                break;
            };
            let page = linear(&p, &a, &o, va, Dir::Next, LINES_MAX).expect("a page");
            assert!(page.next.is_none_or(|next| next > va));
            at = page.next;
        }
    }
}

/// A block entered in the middle of another's instruction starts its own
/// row at its start.
///
/// A `jmp` to the second byte of itself, where `inc eax`
/// begins, lists the `jmp`, then `inc eax` under its label, then `ret`, and
/// the page before each one-row page is the row before it.
#[test]
fn a_block_entered_mid_instruction_starts_its_own_rows() {
    let code: &[u8] = &[
        // ASM: jmp short 0x140001001
        0xeb, 0xff, // ASM: inc eax
        0xc0, // ASM: ret
        0xc3,
    ];
    let p = two_sections(code, &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let page = linear(&p, &a, &o, TEXT, Dir::Next, 8).expect("a page");
    assert_eq!(
        rows(&page),
        [TEXT, TEXT + 1, TEXT + 3],
        "{}",
        page.view.spell()
    );
    assert!(
        line(&page, "L_140001001:").is_some(),
        "{}",
        page.view.spell()
    );
    assert!(
        line(&page, "0x140001001  inc").is_some(),
        "{}",
        page.view.spell()
    );
    let pages = chain(&p, &a, 1);
    for k in 1..pages.len() {
        let back = linear(&p, &a, &o, pages[k].first, Dir::Prev, 1).expect("a page");
        assert_eq!(back.first, pages[k - 1].first, "page {k}");
        assert_eq!(pages[k].prev, Some(pages[k - 1].first), "page {k}");
    }
    let inside = linear(&p, &a, &o, TEXT + 2, Dir::Next, 1).expect("a page");
    assert_eq!(inside.first, TEXT + 1);
}

/// A thread-local `.tbss` the file holds no bytes for, laid over the
/// sections after it as glibc lays it, maps nothing: `.init_array`,
/// `.fini_array` and `.dynamic` keep their headers and their bytes.
#[test]
fn a_thread_local_bss_hides_no_section() {
    let mut bytes = vec![0u8; 0x30];
    bytes[0x18..0x20].copy_from_slice(&0x1122_3344_0566_7788u64.to_le_bytes());
    let mut tbss = Section::mapped(".tbss", 0x3e00, 0x10, 0x10, true, false);
    tbss.file_size = 0;
    let sections = vec![
        Section::mapped(".tdata", 0x3df0, 0, 0x10, true, false),
        tbss,
        Section::mapped(".init_array", 0x3e00, 0x10, 0x8, true, false),
        Section::mapped(".fini_array", 0x3e08, 0x18, 0x8, true, false),
        Section::mapped(".dynamic", 0x3e10, 0x20, 0x10, true, false),
    ];
    let p = Program::raw(bytes, Arch::X86_64, 0, None, sections);
    let a = Analysis::default();
    let page = linear(&p, &a, &Overlay::default(), 0, Dir::Next, 64).expect("a page");
    let text = page.view.spell();
    for want in [
        "; section .init_array rw- 0x3e00..0x3e08",
        "; section .fini_array rw- 0x3e08..0x3e10",
        "; section .dynamic rw- 0x3e10..0x3e20",
        "0x3e08  88 77 66 05 44 33 22 11",
    ] {
        assert!(
            text.lines().any(|l| l.starts_with(want)),
            "no {want:?} in\n{text}"
        );
    }
    assert!(!text.contains(".tbss"), "{text}");
}

/// A block longer than a row table holds lists its first 65536
/// instructions, then one row saying how far it runs on, and a page asked
/// past them starts at that row.
#[test]
fn a_block_past_its_row_table_runs_on_in_one_row() {
    let mut code = vec![0x90u8; 70_000];
    // ASM: ret
    code.push(0xc3);
    let p = two_sections(&code, &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let cut = TEXT + 65_536;
    let page = linear(&p, &a, &o, cut - 1, Dir::Next, 3).expect("a page");
    assert_eq!(rows(&page), [cut - 1, cut], "{}", page.view.spell());
    assert_eq!(page.rows.last().map(|r| r.kind), Some(RowKind::Cut));
    assert!(
        line(
            &page,
            "; 0x1171 bytes of the block to 0x140012171 are past the 65536 instructions a block lists"
        )
        .is_some(),
        "{}",
        page.view.spell()
    );
    let past = linear(&p, &a, &o, cut + 100, Dir::Next, 1).expect("a page");
    assert_eq!(past.first, cut);
}

/// A string that runs on into the next section has its line at its own
/// start; the next section starts with its own header and the bytes no fact
/// there covers, not with the rest of the string.
#[test]
fn a_fact_crossing_into_a_section_keeps_its_line_at_its_start() {
    let mut bytes = vec![0u8; 0x20];
    bytes[0x08..0x18].copy_from_slice(b"abcdefghijklmnop");
    let sections = vec![
        Section::mapped(".a", 0x1000, 0, 0x10, false, false),
        Section::mapped(".b", 0x1010, 0x10, 0x10, false, false),
    ];
    let p = Program::raw(bytes, Arch::X86_64, 0, None, sections);
    let a = Analysis::compute(&p);
    let page = linear(&p, &a, &Overlay::default(), 0, Dir::Next, 16).expect("a page");
    let text = page.view.spell();
    assert!(
        line(
            &page,
            "0x1008  \"abcdefgh\"  ; ascii 16, cut to 8 where the section ends"
        )
        .is_some(),
        "{text}"
    );
    assert!(line(&page, "0x1010  \"").is_none(), "{text}");
    assert!(line(&page, "; section .b").is_some(), "{text}");
    assert!(
        line(&page, "; unexplored 0x1010..0x1020").is_some(),
        "{text}"
    );
}

/// The bytes a data symbol names run on to the next fact inside its own
/// section only: a table at the end of `.rodata` stops where `.data`
/// starts, and `.data` keeps its header and its own uncovered bytes.
#[test]
fn a_named_span_stops_at_its_section_end() {
    let sections = vec![
        Section::mapped(".rodata", 0x1000, 0, 0x10, false, false),
        Section::mapped(".data", 0x1010, 0x10, 0x10, true, false),
    ];
    let mut p = Program::raw(vec![0u8; 0x20], Arch::X86_64, 0, None, sections);
    p.symbols.push(Symbol {
        name: "tbl".to_owned(),
        addr: 0x1008,
        kind: SymbolKind::Data,
    });
    let a = Analysis::compute(&p);
    let page = linear(&p, &a, &Overlay::default(), 0, Dir::Next, 16).expect("a page");
    let text = page.view.spell();
    assert!(
        line(&page, "; data tbl 0x1008..0x1010 (0x8 bytes)").is_some(),
        "{text}"
    );
    assert!(line(&page, "; section .data").is_some(), "{text}");
    assert!(
        line(&page, "; unexplored 0x1010..0x1020").is_some(),
        "{text}"
    );
}

/// A request cancelled before its page is whole answers the rows written by
/// then, says so on its last line, and marks the page cancelled.
#[test]
fn a_cancelled_page_says_it_stopped() {
    let p = image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let cancel = borer_engine::cancel::Cancel::new();
    cancel.raise();
    let page = cancel
        .within(|| linear(&p, &a, &o, RDATA, Dir::Prev, 8))
        .expect("a page");
    assert!(page.cancelled);
    assert!(page.rows.is_empty());
    assert!(
        line(&page, "; cancelled: the page stops here").is_some(),
        "{}",
        page.view.spell()
    );
    assert!(
        !linear(&p, &a, &o, RDATA, Dir::Prev, 8)
            .expect("a page")
            .cancelled
    );
}

/// The types the user applied under one row cost it at most eight lines,
/// then one line counting the rest: ten bytes typed inside a string say so
/// for eight and count two.
#[test]
fn the_types_lost_under_a_row_are_capped_and_counted() {
    let p = image();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    for k in 1..=10 {
        o.applied.insert(RDATA + k, TypeExpr::U8);
    }
    let page = linear(&p, &a, &o, RDATA, Dir::Next, 1).expect("a page");
    let text = page.view.spell();
    let said = text
        .lines()
        .filter(|l| l.starts_with("; the type u8 applied at"))
        .count();
    assert_eq!(said, 8, "{text}");
    assert!(
        line(
            &page,
            "; and 2 more types applied under this row, not laid out"
        )
        .is_some(),
        "{text}"
    );
}

/// A run of edits holds at most one map besides the default overlay's,
/// which stays in force: each edit moves the memo to the new names, and the
/// map read under the old ones goes or moves with it.
#[test]
fn a_run_of_edits_holds_at_most_one_map() {
    let p = image();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    assert!(linear(&p, &a, &o, TEXT, Dir::Next, 16).is_some());
    for step in 0..9u64 {
        let before = o.clone();
        match step % 3 {
            0 => {
                o.applied.insert(RDATA + 0x30 + step, TypeExpr::U8);
            }
            1 => {
                o.names.insert(HELPER, format!("helper_{step}"));
            }
            _ => {
                o.comments.insert(TEXT, format!("note {step}"));
            }
        }
        a.derived.moved(&a, &before, &o);
        assert!(linear(&p, &a, &o, TEXT, Dir::Next, 16).is_some());
        let held = a.derived.held("linear_map");
        assert!(held <= 2, "step {step}: {held} maps held");
    }
}
