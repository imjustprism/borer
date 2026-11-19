//! A search spec is hostile text: an oversized one, a range at the edge
//! of 64 bits and a width no word has are refused, and any text either
//! answers or refuses.

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section};
use borer_engine::search::form::search_tsv;
use borer_engine::search::spec::{SPEC_MAX, parse};
use borer_engine::table::Window;

use super::serial;

/// A one-megabyte pattern is refused with the cap, before any byte of it
/// is read as a pattern.
#[test]
fn a_megabyte_spec_is_refused_with_the_cap() {
    let _serial = serial();
    let spec = format!("bytes:{}", "00 ".repeat(1 << 18));
    let why = parse(&spec).err().unwrap_or_default();
    assert!(why.contains(&SPEC_MAX.to_string()), "{why}");
}

/// A range reaching `u64::MAX` reads; one past 64 bits and a width of three
/// bytes are refused.
#[test]
fn a_range_at_the_edge_of_64_bits_reads_and_one_past_it_is_refused() {
    let _serial = serial();
    let edge = parse("value:0xfffffffffffffff0..0xffffffffffffffff");
    assert!(edge.is_ok(), "{edge:?}");
    assert!(parse("value:0..0x10000000000000000").is_err());
    assert!(parse("value:-0x8000000000000000,signed").is_ok());
    assert!(parse("value:-0x8000000000000001,signed").is_err());
    assert!(parse("value:1,width=3").is_err());
    let all = parse("value:0..0xffffffffffffffff,width=8");
    assert!(all.is_ok(), "{all:?}");
}

/// Texts built from the grammar's pieces, joined at random, each answer
/// or refuse over a program whose code and data are the same bytes.
#[test]
fn any_spec_answers_or_refuses() {
    let _serial = serial();
    let pieces = [
        "bytes:",
        "text:",
        "value:",
        "in=",
        "and",
        "or",
        "minus",
        "0x",
        "..",
        ",",
        "4?",
        "??",
        "?",
        "-",
        "width=8",
        "signed",
        "align=4096",
        "disp",
        "order=be",
        ".text",
        "0x1000",
        "ffffffffffffffff",
        " ",
        ":",
        "=",
        "\u{e9}",
        "\t",
        "\n",
    ];
    let bytes = vec![0x90u8; 0x100];
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x80, false, true),
            Section::mapped(".data", 0x2000, 0x80, 0x80, true, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let mut x = 0x0bad_5eed_u32;
    for _ in 0..2000 {
        let mut spec = String::new();
        for _ in 0..1 + x % 9 {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            spec.push_str(pieces[usize::try_from(x).unwrap_or(0) % pieces.len()]);
        }
        if let Ok(text) = search_tsv(&p, &a, &o, &spec, Window::first(50)) {
            assert!(text.starts_with("# search "), "{spec:?}: {text}");
        }
    }
}
