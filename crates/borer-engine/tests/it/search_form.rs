//! The search form: values in data words, scopes, set operations, the
//! table it answers, and the refusals naming their column.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, BasicBlock, BlockTerm, Overlay};
use borer_engine::program::{Arch, Program, Section};
use borer_engine::search::form::{Found, Matched, search, search_tsv};
use borer_engine::search::spec::{Find, Order, Text, parse};
use borer_engine::table::Window;

/// Builds an x86-64 program with a value planted in code and data.
///
/// `.text` at 0x1000 (executable) holds
/// `mov ecx, 0x12345678; cmp eax, 0x12345678; mov eax, -1; ret`, and
/// `.data` at 0x2000 holding 0x12345678 as a little-endian dword at
/// 0x2000, as a big-endian one at 0x2004, the words 0x1000, 0x10ff, 0x1100
/// and 0x0fff from 0x2008, -1 as a dword at 0x2010, and 0x12345678
/// unaligned at 0x2015.
pub(crate) fn planted() -> (Program, Analysis) {
    let mut bytes = vec![0u8; 0x200];
    let code = [
        0xb9, 0x78, 0x56, 0x34, 0x12, 0x3d, 0x78, 0x56, 0x34, 0x12, 0xb8, 0xff, 0xff, 0xff, 0xff,
        0xc3,
    ];
    bytes[..0x100].fill(0xcc);
    bytes[..code.len()].copy_from_slice(&code);
    let data = [
        0x78, 0x56, 0x34, 0x12, 0x12, 0x34, 0x56, 0x78, 0x00, 0x10, 0xff, 0x10, 0x00, 0x11, 0xff,
        0x0f, 0xff, 0xff, 0xff, 0xff, 0x00, 0x78, 0x56, 0x34, 0x12,
    ];
    bytes[0x100..0x100 + data.len()].copy_from_slice(&data);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x100, false, true),
            Section::mapped(".data", 0x2000, 0x100, 0x100, true, false),
        ],
    );
    let a = Analysis::compute(&p);
    (p, a)
}

/// Runs a spec over the planted program.
///
/// # Errors
///
/// When the spec does not read or the search refuses.
fn hits(spec: &str) -> Result<Vec<Found>, String> {
    let (p, a) = planted();
    search(&p, &a, &Overlay::default(), &parse(spec)?)
}

/// Returns the addresses of a spec's hits over the planted program.
///
/// # Errors
///
/// As [`hits`].
fn vas(spec: &str) -> Result<Vec<u64>, String> {
    Ok(hits(spec)?.iter().filter_map(|h| h.va).collect())
}

/// A value is found as an aligned data word in the byte order asked, the
/// little-endian one by default; the bytes spell it in code too.
#[test]
fn a_value_is_found_as_a_data_word_in_its_byte_order() {
    let le = hits("value:0x12345678 and in=.data").expect("searches");
    assert_eq!(
        le.iter().map(|h| (h.va, h.off)).collect::<Vec<_>>(),
        vec![(Some(0x2000), Some(0x100))]
    );
    assert_eq!(
        le[0].matched,
        Matched::Data {
            width: 4,
            order: Order::Le
        }
    );
    assert_eq!(
        vas("value:0x12345678,order=be and in=.data"),
        Ok(vec![0x2004])
    );
    assert_eq!(
        vas("value:0x12345678,align=1 and in=.data"),
        Ok(vec![0x2000, 0x2015])
    );
    let unaligned = hits("value:0x12345678,align=1").expect("searches");
    let in_code = |h: &Found| matches!(h.matched, Matched::Data { .. }) && h.va < Some(0x2000);
    assert!(!unaligned.iter().any(in_code), "{unaligned:?}");
    assert_eq!(
        vas("bytes:78 56 34 12"),
        Ok(vec![0x1001, 0x1006, 0x2000, 0x2015])
    );
}

/// A range takes both ends and nothing past them; a signed value reads
/// words as two's complement.
#[test]
fn ranges_and_signs_read_words_as_numbers() {
    assert_eq!(
        vas("value:0x1000..0x10ff,width=2"),
        Ok(vec![0x2008, 0x200a])
    );
    assert_eq!(
        vas("value:-1,width=4,signed and in=.data"),
        Ok(vec![0x2010])
    );
    assert_eq!(vas("value:0xffffffff and in=.data"), Ok(vec![0x2010]));
    assert!(vas("value:-1,width=4,signed,order=be").is_ok_and(|v| v.contains(&0x2010)));
}

/// `and`, `or` and `minus` combine by address, and `in=` narrows to a
/// section, a range or a whole function, not only its entry.
#[test]
fn clauses_combine_by_address() {
    let le = "value:0x12345678";
    let data = "and in=.data";
    assert_eq!(
        vas(&format!("{le},align=1 {data} minus in=0x2000..0x2003")),
        Ok(vec![0x2015])
    );
    assert_eq!(
        vas(&format!("{le},align=1 and in=.data")),
        Ok(vec![0x2000, 0x2015])
    );
    assert_eq!(
        vas(&format!("{le} or {le},order=be {data}")),
        Ok(vec![0x2000, 0x2004])
    );
    assert_eq!(
        vas(&format!("{le} {data} and {le},align=1")),
        Ok(vec![0x2000])
    );
    assert_eq!(
        vas(&format!("{le},align=1 {data} minus {le}")),
        Ok(vec![0x2015])
    );
    assert_eq!(vas("bytes:3d 78 and in=0x1000"), Ok(vec![0x1005]));
    assert_eq!(vas("bytes:3d 78 minus in=0x1000"), Ok(Vec::new()));
    let union = hits("bytes:78 56 34 12 or value:0x12345678 and in=.data").expect("searches");
    assert!(
        union.iter().all(|h| h.matched == Matched::Bytes),
        "{union:?}"
    );
}

/// The table counts every hit, shows the page asked with the line naming
/// the next one, and says how each hit matched.
#[test]
fn the_table_pages_and_says_how_each_hit_matched() {
    let (p, a) = planted();
    let o = Overlay::default();
    let window = Window {
        skip: 1,
        limit: 2,
        again: Some("borer://search/bytes:78 56 34 12"),
    };
    let text = search_tsv(&p, &a, &o, "bytes:78 56 34 12", window).expect("answers");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(
        lines[0],
        "# search bytes:78 56 34 12: 4 hits, showing 2 of 4 from 1"
    );
    assert_eq!(lines[1], "va\toff\tfunction\tsection\tmatched");
    assert!(lines[2].starts_with("0x1006\t0x6\t"), "{text}");
    assert!(lines[2].ends_with("\t.text\tbytes"), "{text}");
    assert_eq!(lines[3], "0x2000\t0x100\t-\t.data\tbytes");
    assert_eq!(
        lines[4],
        "# 1 more; borer://search/bytes:78 56 34 12!offset=3 for the next page"
    );
    let value = search_tsv(&p, &a, &o, "value:0x12345678", Window::first(10)).expect("answers");
    assert!(value.contains("\tdata width=4 order=le\n"), "{value}");
    assert!(
        value.lines().nth(1).is_some_and(|l| l.starts_with("# ")),
        "{value}"
    );
    let text = search_tsv(&p, &a, &o, "text:XV4", Window::first(10)).expect("answers");
    assert!(text.contains("\t.data\ttext\n"), "{text}");
}

/// A spec that does not read is refused at its column with the form
/// expected there.
#[test]
fn a_bad_spec_is_refused_at_its_column() {
    let refused = |spec: &str, want: &str| {
        let why = parse(spec).expect_err(spec);
        assert!(why.contains(want), "{spec}: {why}");
    };
    refused("value:0x10,width=3", "column 12: width is 1, 2, 4 or 8");
    refused("value:0x10,nope", "column 12: 'nope' is no value option");
    refused("value:zz", "column 7: 'zz' is not a number");
    refused("value:5..4", "the range ends below its start");
    refused("value:-1", "a negative value needs signed");
    refused("value:0x10000,width=2", "does not fit width=2");
    refused("value:0x10,align=3", "align is a power of two");
    refused("find:x", "column 1: 'find' is no clause");
    refused("bytes:48 zz", "column 10: 'zz' is not a byte");
    refused("bytes:48 and", "ends after an operation");
    refused("and bytes:48", "column 1: and needs a clause before it");
    refused("in=.text and bytes:48", "column 1: in= narrows");
    refused("bytes:48 or in=.text", "follows and or minus");
    refused("bytes:48 minus in=", "names no place");
    refused("text:", "names no text");
    refused("", "the spec is empty");
    refused("text:日本 and zz", "column 13: 'zz' is no clause");
    refused("text:\"open", "column 1: the quoted text is not closed");
    refused("text:\"a\"b", "column 9: a quoted text ends its clause");
}

/// A quoted text holds the words that would end an unquoted one, and a
/// doubled quote stands for one quote.
#[test]
fn a_quoted_text_holds_operator_words_and_quotes() {
    let one = parse("text:\"Save or Discard\" minus in=.data").expect("reads");
    let want = |t: &str| Find::Text(Text::new(t).expect("a text"));
    assert_eq!(one.finds().collect::<Vec<_>>(), [&want("Save or Discard")]);
    let quoted = parse("text:\"say \"\"hi\"\"\"").expect("reads");
    assert_eq!(quoted.finds().next(), Some(&want("say \"hi\"")));
    assert_eq!(
        parse("text:a\"b").expect("reads").finds().next(),
        Some(&want("a\"b"))
    );
}

/// A place that does not resolve is refused when the spec runs.
#[test]
fn a_place_that_does_not_resolve_is_refused() {
    let (p, a) = planted();
    let o = Overlay::default();
    for place in ["no_such_name", "0x3000", "0x2000..0x1000"] {
        let spec = parse(&format!("bytes:78 minus in={place}")).expect("reads");
        assert!(search(&p, &a, &o, &spec).is_err(), "{place}");
    }
}

/// The resource answers through the engine's reader, refuses a bad spec
/// before anything is read, and pages by its suffixes.
#[test]
fn the_resource_answers_and_pages() {
    let (p, a) = planted();
    let o = Overlay::default();
    let read = |uri| borer_engine::answer::ask(&p, &a, &o, uri).expect("the engine answers it");
    let text =
        read("borer://search/value:0x12345678,align=1 and in=.data!limit=1").expect("answers");
    assert!(
        text.starts_with(
            "# search value:0x12345678,align=1 and in=.data: 2 hits, showing 1 of 2 from 0\n"
        ),
        "{text}"
    );
    assert!(text.contains("!offset=1 for the next page"), "{text}");
    let need = borer_engine::answer::need("search", Some("value:-"));
    assert!(need.is_some_and(|n| n.is_err()));
}

/// A value is found as an immediate of each instruction that states it,
/// at the instruction's address, beside its data word; executable bytes
/// stay out of the data tier however aligned.
#[test]
fn a_value_is_found_in_instruction_operands() {
    let imm = Matched::Immediate { operand: 1 };
    let found: Vec<(Option<u64>, Matched)> = hits("value:0x12345678")
        .expect("searches")
        .iter()
        .map(|h| (h.va, h.matched))
        .collect();
    assert_eq!(
        found,
        vec![
            (Some(0x1000), imm),
            (Some(0x1005), imm),
            (
                Some(0x2000),
                Matched::Data {
                    width: 4,
                    order: Order::Le
                }
            )
        ]
    );
    assert_eq!(
        vas("value:0x12345678,align=1"),
        Ok(vec![0x1000, 0x1005, 0x2000, 0x2015])
    );
    assert_eq!(
        vas("value:0x12345678,order=be"),
        Ok(vec![0x1000, 0x1005, 0x2004])
    );
    assert_eq!(vas("value:-1,width=4,signed"), Ok(vec![0x100a, 0x2010]));
    assert_eq!(vas("value:0x12345678 minus in=0x1000"), Ok(vec![0x2000]));
    assert_eq!(
        vas("value:0x12345678 and in=0x1000"),
        Ok(vec![0x1000, 0x1005])
    );
}

/// Returns the addresses and matches of a spec's hits over one function
/// of `code` at 0x1000 in the architecture given.
///
/// # Errors
///
/// When the spec does not read or the search refuses.
fn code_hits(arch: Arch, code: &[u8], spec: &str) -> Result<Vec<(u64, Matched)>, String> {
    let p = Program::raw(
        code.to_vec(),
        arch,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text",
            0x1000,
            0,
            u64::try_from(code.len()).unwrap_or(0),
            false,
            true,
        )],
    );
    let a = Analysis::compute(&p);
    Ok(search(&p, &a, &Overlay::default(), &parse(spec)?)?
        .iter()
        .filter_map(|h| Some((h.va?, h.matched)))
        .collect())
}

/// Each instruction set states its constants.
///
/// A displacement is a hit only with `disp`; an immediate the encoding
/// sign-extends is read at its operand's width; arm64 `mov w0, #0x1234`,
/// ARM32 `movw r0, #0x1234` and RISC-V `lui a0, 0x12345` state theirs.
#[test]
fn each_instruction_set_states_its_constants() {
    let load = [0x8b, 0x83, 0x34, 0x12, 0x00, 0x00, 0xc3];
    assert_eq!(
        code_hits(Arch::X86_64, &load, "value:0x1234"),
        Ok(Vec::new())
    );
    assert_eq!(
        code_hits(Arch::X86_64, &load, "value:0x1234,disp"),
        Ok(vec![(0x1000, Matched::Displacement { operand: 1 })])
    );
    let imm = |at| Ok(vec![(at, Matched::Immediate { operand: 1 })]);
    let cmp = [0x83, 0xf8, 0xff, 0xc3];
    assert_eq!(
        code_hits(Arch::X86_64, &cmp, "value:0xffffffff"),
        imm(0x1000)
    );
    assert_eq!(
        code_hits(Arch::X86_64, &cmp, "value:-1,signed"),
        imm(0x1000)
    );
    let a64 = [0x80, 0x46, 0x82, 0x52, 0xc0, 0x03, 0x5f, 0xd6];
    assert_eq!(code_hits(Arch::Arm64, &a64, "value:0x1234"), imm(0x1000));
    let a32 = [0x34, 0x02, 0x01, 0xe3, 0x1e, 0xff, 0x2f, 0xe1];
    assert_eq!(code_hits(Arch::Arm, &a32, "value:0x1234"), imm(0x1000));
    let rv = [0x37, 0x55, 0x34, 0x12, 0x67, 0x80, 0x00, 0x00];
    let shifted = |at| Ok(vec![(at, Matched::Shifted { operand: 1 })]);
    assert_eq!(
        code_hits(Arch::RiscV64, &rv, "value:0x12345000"),
        shifted(0x1000)
    );
}

/// An immediate an instruction shifts is sought as the value it
/// contributes, and the hit says shifted.
///
/// ARM32 `movt r0, #0x1234` is 0x12340000; a RIP-relative operand is the
/// address it reaches, searched with `disp`, and says address.
#[test]
fn shifted_immediates_and_reached_addresses_say_so() {
    let movt = [0x34, 0x02, 0x41, 0xe3, 0x1e, 0xff, 0x2f, 0xe1];
    assert_eq!(
        code_hits(Arch::Arm, &movt, "value:0x12340000"),
        Ok(vec![(0x1000, Matched::Shifted { operand: 1 })])
    );
    assert_eq!(code_hits(Arch::Arm, &movt, "value:0x1234"), Ok(Vec::new()));
    let lea = [0x48, 0x8d, 0x05, 0x00, 0x01, 0x00, 0x00, 0xc3];
    assert_eq!(
        code_hits(Arch::X86_64, &lea, "value:0x1107"),
        Ok(Vec::new())
    );
    assert_eq!(
        code_hits(Arch::X86_64, &lea, "value:0x1107,disp"),
        Ok(vec![(0x1000, Matched::Address { operand: 1 })])
    );
}

/// Returns a raw x86-64 program of `bytes` as one section at 0x10000.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `sections` - The sections, each `(name, file offset, size, executable)`.
fn raw(bytes: Vec<u8>, sections: &[(&str, u64, u64, bool)]) -> (Program, Analysis) {
    let sections = sections
        .iter()
        .map(|&(name, off, size, x)| Section::mapped(name, 0x10000 + off, off, size, !x, x))
        .collect();
    let p = Program::raw(bytes, Arch::X86_64, 0, None, sections);
    (p, Analysis::default())
}

/// Returns the addresses of a spec's hits over a program.
///
/// # Errors
///
/// When the spec does not read or the search refuses.
fn vas_in(p: &Program, a: &Analysis, spec: &str) -> Result<Vec<u64>, String> {
    Ok(search(p, a, &Overlay::default(), &parse(spec)?)?
        .iter()
        .filter_map(|h| h.va)
        .collect())
}

/// A match that straddles a 1 MiB chunk boundary is found once, by the
/// search form and by the tool's walk alike: a byte pattern, a masked one,
/// a text and a UTF-16 text.
#[test]
fn a_match_straddling_a_chunk_boundary_is_found() {
    let mut bytes = vec![0u8; 4 << 20];
    bytes[0xF_FFFE..0x10_0002].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    bytes[0x1F_FFFD..0x20_0005].copy_from_slice(b"straddle");
    let wide: Vec<u8> = "wide".encode_utf16().flat_map(u16::to_le_bytes).collect();
    bytes[0x2F_FFFA..0x30_0002].copy_from_slice(&wide);
    let (p, a) = raw(bytes, &[(".text", 0, 4 << 20, true)]);
    assert_eq!(vas_in(&p, &a, "bytes:de ad be ef"), Ok(vec![0x10_FFFE]));
    assert_eq!(vas_in(&p, &a, "bytes:de a? be ef"), Ok(vec![0x10_FFFE]));
    assert_eq!(vas_in(&p, &a, "text:STRADDLE"), Ok(vec![0x20_FFFD]));
    assert_eq!(vas_in(&p, &a, "text:wide"), Ok(vec![0x30_FFFA]));
    let pattern = borer_engine::search::parse_masked("de ad be ef").expect("a pattern");
    assert_eq!(
        borer_engine::search::find_masked(&p, &pattern, 0)
            .expect("the search answers")
            .total,
        1
    );
    assert_eq!(
        borer_engine::search::find_text(&p, "wide", 0)
            .expect("the search answers")
            .total,
        1
    );
}

/// `and in=` scopes the scan before it holds hits: a byte found half a
/// million times in the file and 16 times in the scope answers the 16,
/// where a filter after the scan would refuse at the cap.
#[test]
fn a_scope_narrows_the_scan_before_the_cap() {
    let (p, a) = raw(vec![0u8; 512 << 10], &[(".data", 0, 512 << 10, false)]);
    let inside = vas_in(&p, &a, "bytes:00 and in=0x10000..0x1000f").expect("answers");
    assert_eq!(inside.len(), 16);
    assert!(vas_in(&p, &a, "bytes:00").is_err_and(|why| why.contains("262144")));
}

/// `in=<section>` covers the extent the row's section column names: a
/// section with no virtual size but file bytes, and every section of one
/// name.
#[test]
fn a_section_scope_covers_its_rows_extent_and_its_namesakes() {
    let mut bytes = vec![0u8; 0x600];
    for at in [0x10, 0x210, 0x410] {
        bytes[at] = 0x5a;
    }
    let (mut p, a) = raw(
        bytes,
        &[
            (".odd", 0, 0x200, false),
            (".dup", 0x200, 0x200, false),
            (".dup", 0x400, 0x200, false),
        ],
    );
    p.sections[0].vsize = 0;
    assert_eq!(vas_in(&p, &a, "bytes:5a and in=.odd"), Ok(vec![0x10010]));
    assert_eq!(
        vas_in(&p, &a, "bytes:5a and in=.dup"),
        Ok(vec![0x10210, 0x10410])
    );
}

/// Two sections that map the same file bytes at different addresses are
/// walked once, with a hit at each address.
///
/// A byte they share is a hit at both addresses, by the form and by the
/// tool's walk, as a value is; `in=.b` keeps the one `.b` maps.
#[test]
fn sections_sharing_file_bytes_are_walked_once() {
    let mut bytes = vec![0u8; 0x100];
    bytes[0x20] = 0x5a;
    let sections = vec![
        Section::mapped(".a", 0x10000, 0, 0x100, true, false),
        Section::mapped(".b", 0x20000, 0, 0x100, true, false),
    ];
    let p = Program::raw(bytes, Arch::X86_64, 0, None, sections);
    let a = Analysis::default();
    assert_eq!(vas_in(&p, &a, "bytes:5a"), Ok(vec![0x10020, 0x20020]));
    assert_eq!(vas_in(&p, &a, "bytes:5a and in=.b"), Ok(vec![0x20020]));
    assert_eq!(vas_in(&p, &a, "value:0x5a"), Ok(vec![0x10020, 0x20020]));
    let pattern = borer_engine::search::parse_masked("5a").expect("a pattern");
    assert_eq!(
        borer_engine::search::find_masked(&p, &pattern, 0)
            .expect("the search answers")
            .total,
        2
    );
}

/// An arm64 immediate is the value the listing prints: `movn` inverted, a
/// bitfield move as its `lsl` alias's shift, `movz` and `add` with their
/// shifts folded in.
#[test]
fn arm64_immediates_are_what_the_listing_prints() {
    let ret = [0xc0, 0x03, 0x5f, 0xd6];
    let one = |word: [u8; 4], spec: &str| {
        let code = [word, ret].concat();
        code_hits(Arch::Arm64, &code, spec).map(|h| h.iter().map(|x| x.0).collect::<Vec<_>>())
    };
    let movn = [0xa0, 0x02, 0x80, 0x12];
    assert_eq!(one(movn, "value:-22,signed"), Ok(vec![0x1000]));
    assert_eq!(one(movn, "value:0xffffffea"), Ok(vec![0x1000]));
    assert_eq!(one(movn, "value:21"), Ok(Vec::new()));
    assert_eq!(one([0x20, 0xf0, 0x7d, 0xd3], "value:3"), Ok(vec![0x1000]));
    assert_eq!(
        one([0x80, 0x46, 0xa2, 0xd2], "value:0x12340000"),
        Ok(vec![0x1000])
    );
    assert_eq!(
        one([0x20, 0x04, 0x40, 0x91], "value:0x1000"),
        Ok(vec![0x1000])
    );
}

/// An ARM32 doubleword load's offset is a displacement of its third
/// operand, and an x86 displacement under an address-size prefix is read
/// at 32 bits.
#[test]
fn displacements_follow_the_operand_and_the_address_size() {
    let ldrd = [0xd8, 0x00, 0xc2, 0xe1, 0x1e, 0xff, 0x2f, 0xe1];
    assert_eq!(
        code_hits(Arch::Arm, &ldrd, "value:8,disp"),
        Ok(vec![(0x1000, Matched::Displacement { operand: 2 })])
    );
    let prefixed = [0x67, 0x8b, 0x41, 0xf8, 0xc3];
    assert_eq!(
        code_hits(Arch::X86_64, &prefixed, "value:-8,signed,disp"),
        Ok(vec![(0x1000, Matched::Displacement { operand: 1 })])
    );
}

/// A script's `find_bytes` reads the one pattern parser: a nibble
/// answers, and a bad token raises the parser's refusal.
#[test]
fn a_script_finds_bytes_through_the_one_parser() {
    let run = |code: &str| {
        let (p, a) = planted();
        borer_engine::script::run(
            std::sync::Arc::new(p),
            std::sync::Arc::new(a),
            std::sync::Arc::default(),
            code,
            &[],
        )
    };
    let found = run(r#"print(find_bytes("3d 7?"));"#).expect("runs");
    assert!(
        found.output.join("\n").contains("4101"),
        "{:?}",
        found.output
    );
    let refused = run(r#"print(find_bytes("3d zz"));"#).expect_err("refused");
    assert!(refused.contains("column 4"), "{refused}");
}

/// `in=<function>` keeps to that function's own blocks: a tail two
/// functions jump into is in each of them.
#[test]
fn a_function_scope_holds_its_own_blocks() {
    let mut code = vec![0xccu8; 0x30];
    code[..10].copy_from_slice(&[0xe8, 0x0b, 0, 0, 0, 0xe9, 0x16, 0, 0, 0]);
    code[0x10..0x1a].copy_from_slice(&[0xb8, 2, 0, 0, 0, 0xe9, 0x06, 0, 0, 0]);
    code[0x20..0x26].copy_from_slice(&[0x3d, 0x78, 0x56, 0x34, 0x12, 0xc3]);
    let p = Program::raw(
        code,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x30, false, true)],
    );
    let a = Analysis::compute(&p);
    let owners: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.blocks.iter().any(|b| (b.start..b.end).contains(&0x1020)))
        .map(|f| f.entry)
        .collect();
    assert!(owners.len() >= 2, "owners of the tail: {owners:x?}");
    for f in owners {
        assert_eq!(
            vas_in(&p, &a, &format!("value:0x12345678 and in={f:#x}")),
            Ok(vec![0x1020]),
            "in={f:#x}"
        );
    }
}

/// A value with no width is sought at the narrowest that holds it, and
/// when that finds more hits than a search holds, the refusal tells the
/// agent to give a width or a scope, with an example of each.
#[test]
fn a_value_finding_too_many_hits_says_to_add_a_width_or_a_scope() {
    let (p, a) = raw(vec![0; 300_000], &[(".data", 0, 300_000, false)]);
    let why = vas_in(&p, &a, "value:0").expect_err("too many hits is refused");
    assert!(why.contains("width=4") && why.contains("in=.data"), "{why}");
}

/// Nine sections mapping the same bytes at nine addresses are refused by
/// every byte finder, never answered with no hit.
#[test]
fn a_byte_mapped_at_too_many_addresses_is_refused_everywhere() {
    let p = nine_mappings();
    let pattern = borer_engine::search::parse_masked("5a").unwrap_or_else(|e| panic!("{e}"));
    let masked = borer_engine::search::find_masked(&p, &pattern, 0);
    assert!(
        masked
            .as_ref()
            .is_err_and(|why| why.contains("more than 8")),
        "{masked:?}"
    );
    let bytes = borer_engine::search::find_bytes(&p, &[Some(0x5a)], 0);
    assert!(bytes.is_err(), "{bytes:?}");
    let text = borer_engine::search::find_text(&p, "Z", 0);
    assert!(text.is_err(), "{text:?}");
    let a = Analysis::default();
    assert!(vas_in(&p, &a, "bytes:5a").is_err_and(|why| why.contains("more than 8")));
    assert!(vas_in(&p, &a, "value:0x5a").is_err_and(|why| why.contains("more than 8")));
}

/// Returns a program of nine sections mapping the same 0x100 bytes of
/// 0x5a (`pop rdx` as x86-64 code) at 0x10000, 0x20000, ... 0x90000.
fn nine_mappings() -> Program {
    let sections = (0..9u64)
        .map(|k| Section::mapped(".m", 0x10000 * (k + 1), 0, 0x100, true, false))
        .collect();
    Program::raw(vec![0x5a; 0x100], Arch::X86_64, 0, None, sections)
}

/// Asserts an answer is the refusal naming the eight-address limit.
fn assert_refused<T: std::fmt::Debug>(got: &Result<T, String>) {
    assert!(
        got.as_ref()
            .is_err_and(|why| why.contains("more than 8 addresses")),
        "{got:?}"
    );
}

/// A code signature over a byte mapped at nine addresses is refused, never
/// counted as matching nowhere.
#[test]
fn a_signature_over_too_many_mappings_is_refused() {
    let p = nine_mappings();
    assert_refused(
        &borer_engine::analysis::render::signature(&p, 0x10000, None).map(|s| s.matches),
    );
}

/// A script's `find_bytes` and `find_text` over a byte mapped at nine
/// addresses raise the refusal, never an empty list.
#[test]
fn a_script_search_over_too_many_mappings_is_refused() {
    let run = |code: &str| {
        borer_engine::script::run(
            std::sync::Arc::new(nine_mappings()),
            std::sync::Arc::new(Analysis::default()),
            std::sync::Arc::default(),
            code,
            &[],
        )
        .map(|r| r.output)
    };
    assert_refused(&run(r#"print(find_bytes("5a").len());"#));
    assert_refused(&run(r#"print(find_text("Z").len());"#));
}

/// A decompiled text's string literal looked up in a file mapping a byte
/// at nine addresses is refused, never read as a literal held nowhere.
#[test]
fn a_literal_lookup_over_too_many_mappings_is_refused() {
    let p = nine_mappings();
    let a = Analysis::compute(&p);
    let text = "// signature: uint64_t f(void)\nreturn \"Z\";\n";
    assert_refused(&borer_engine::analysis::decompile::unset_reads(
        &p,
        &a,
        &Overlay::default(),
        0x10000,
        text,
    ));
}

/// An arm64 `movn` with a shift is sought as the value it writes, the
/// inverse of its shifted immediate, and says shifted.
#[test]
fn an_arm64_shifted_movn_says_shifted() {
    let ret = [0xc0, 0x03, 0x5f, 0xd6];
    let movn = [0x80, 0x46, 0xa2, 0x12];
    assert_eq!(
        code_hits(Arch::Arm64, &[movn, ret].concat(), "value:0xedcbffff"),
        Ok(vec![(0x1000, Matched::Shifted { operand: 1 })])
    );
    assert_eq!(
        code_hits(Arch::Arm64, &[movn, ret].concat(), "value:0x12340000"),
        Ok(Vec::new())
    );
}

/// Every instruction a block reaches states its constants, even where a
/// misaligned block decoded past a gap an aligned one left.
///
/// `mov eax, 5; mov eax, eax; mov eax, 0x22222222; ret` from 0x1000 is
/// cut into blocks 0x1000..0x1007, a misaligned 0x1001..0x100d (`add eax,
/// 0x89000000; sar byte [rax+0x22222222], 0xc3`) and 0x1005..0x100d, so
/// only the last reaches the `mov` at 0x1007.
#[test]
fn overlapping_misaligned_blocks_leave_no_instruction_undecoded() {
    let mut code = vec![0xccu8; 0x20];
    code[..13].copy_from_slice(&[
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax,5
        0x89, 0xc0, // ASM: mov eax,eax
        0xb8, 0x22, 0x22, 0x22, 0x22, // ASM: mov eax,22222222h
        0xc3, // ASM: ret
    ]);
    let p = Program::raw(
        code,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x20, false, true)],
    );
    let mut a = Analysis::compute(&p);
    a.functions.retain(|f| f.entry == 0x1000);
    let f = a.functions.first_mut().expect("a function at the entry");
    f.blocks = [(0x1000, 0x1007), (0x1001, 0x100d), (0x1005, 0x100d)]
        .into_iter()
        .map(|(start, end)| BasicBlock {
            start,
            end,
            term: BlockTerm::Fall,
            successors: smallvec::SmallVec::new(),
        })
        .collect();
    let spec = parse("value:0x22222222").expect("a spec");
    let hits: Vec<_> = search(&p, &a, &Overlay::default(), &spec)
        .expect("the search answers")
        .iter()
        .filter_map(|h| Some((h.va?, h.matched)))
        .collect();
    assert_eq!(hits, vec![(0x1007, Matched::Immediate { operand: 1 })]);
}

/// An arm64 move-wide with a shift and a `movi` with `msl` are sought as
/// the value they contribute, and say shifted.
#[test]
fn arm64_shifted_moves_say_so() {
    let ret = [0xc0, 0x03, 0x5f, 0xd6];
    let movz = [0x80, 0x46, 0xa2, 0xd2];
    assert_eq!(
        code_hits(Arch::Arm64, &[movz, ret].concat(), "value:0x12340000"),
        Ok(vec![(0x1000, Matched::Shifted { operand: 1 })])
    );
    let movi = [0x40, 0xc6, 0x00, 0x4f];
    assert_eq!(
        code_hits(Arch::Arm64, &[movi, ret].concat(), "value:0x12ff"),
        Ok(vec![(0x1000, Matched::Shifted { operand: 1 })])
    );
}

/// Returns a big-endian ELF64 whose one data section at 0x10000 holds
/// the word 0x12345678 in its first four bytes.
fn big_endian_elf() -> Vec<u8> {
    let mut b = vec![0u8; 0x68 + 3 * 64];
    b[..8].copy_from_slice(&[0x7f, b'E', b'L', b'F', 2, 2, 1, 0]);
    b[16..18].copy_from_slice(&2u16.to_be_bytes());
    b[18..20].copy_from_slice(&21u16.to_be_bytes());
    b[20..24].copy_from_slice(&1u32.to_be_bytes());
    b[40..48].copy_from_slice(&0x68u64.to_be_bytes());
    b[52..54].copy_from_slice(&64u16.to_be_bytes());
    b[54..56].copy_from_slice(&56u16.to_be_bytes());
    b[58..60].copy_from_slice(&64u16.to_be_bytes());
    b[60..62].copy_from_slice(&3u16.to_be_bytes());
    b[62..64].copy_from_slice(&2u16.to_be_bytes());
    b[0x40..0x44].copy_from_slice(&0x1234_5678u32.to_be_bytes());
    b[0x50..0x61].copy_from_slice(b"\0.data\0.shstrtab\0");
    let header = |b: &mut Vec<u8>,
                  at: usize,
                  name: u32,
                  kind: u32,
                  flags: u64,
                  va: u64,
                  off: u64,
                  size: u64| {
        b[at..at + 4].copy_from_slice(&name.to_be_bytes());
        b[at + 4..at + 8].copy_from_slice(&kind.to_be_bytes());
        b[at + 8..at + 16].copy_from_slice(&flags.to_be_bytes());
        b[at + 16..at + 24].copy_from_slice(&va.to_be_bytes());
        b[at + 24..at + 32].copy_from_slice(&off.to_be_bytes());
        b[at + 32..at + 40].copy_from_slice(&size.to_be_bytes());
        b[at + 48..at + 56].copy_from_slice(&1u64.to_be_bytes());
    };
    header(&mut b, 0x68 + 64, 1, 1, 3, 0x10000, 0x40, 0x10);
    header(&mut b, 0x68 + 128, 7, 3, 0, 0, 0x50, 0x11);
    b
}

/// A value with no order is read in the file's own byte order: a big-
/// endian ELF's data word is found as written, and says order=be.
#[test]
fn a_value_is_read_in_the_file_s_own_byte_order() {
    let p = Program::from_bytes(std::path::PathBuf::from("be.elf"), big_endian_elf())
        .unwrap_or_else(|e| panic!("{e}"));
    let got = search(
        &p,
        &Analysis::default(),
        &Overlay::default(),
        &parse("value:0x12345678,width=4").unwrap_or_else(|e| panic!("{e}")),
    );
    let got = got.map(|h| h.iter().map(|f| (f.va, f.matched)).collect::<Vec<_>>());
    assert_eq!(
        got,
        Ok(vec![(
            Some(0x10000),
            Matched::Data {
                width: 4,
                order: Order::Be
            }
        )])
    );
}
