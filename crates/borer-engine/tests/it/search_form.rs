//! The search form: values in data words, scopes, set operations, the
//! table it answers, and the refusals naming their column.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::num::NonZeroUsize;

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section};
use borer_engine::progress::Workers;
use borer_engine::search::form::{Found, Matched, search, search_tsv};
use borer_engine::search::spec::{Order, parse};
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
        vec![(Some(0x2000), 0x100)]
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

/// A search answers the same bytes at one worker and at sixteen.
#[test]
fn a_search_answers_alike_at_any_worker_count() {
    let (p, a) = planted();
    let o = Overlay::default();
    let spec = "value:0x12345678,align=1 or bytes:4? ?? or text:xv minus in=0x2010..0x2013";
    let at = |n| {
        Workers(NonZeroUsize::new(n).unwrap_or(NonZeroUsize::MIN))
            .within(|| search_tsv(&p, &a, &o, spec, Window::first(500)))
    };
    assert_eq!(at(1), at(16));
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
