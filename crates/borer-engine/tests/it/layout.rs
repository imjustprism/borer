//! Raw code and memory dumps loaded at a caller-stated layout: the bytes
//! map where the caller says, and every analysis reads them as it reads
//! a parsed image.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::disasm;
use borer_engine::isa::Isa;
use borer_engine::layout::{Layout, REGIONS_MAX, parse_arch};
use borer_engine::program::{Arch, BinaryFormat, Feature, Program};

use crate::decompiled::decompiled;

/// An x86-64 routine that calls a local function and adds one to what it
/// returns, then the function, which returns 42: two functions, the
/// first returning 43.
const X64_CODE: &[u8] = &[
    // ASM: call 0x1000b (from 0x10000)
    0xe8, 0x06, 0x00, 0x00, 0x00, //
    // ASM: add rax, 1
    0x48, 0x83, 0xc0, 0x01, //
    // ASM: ret
    0xc3, //
    // ASM: int3
    0xcc, //
    // ASM: mov eax, 42
    0xb8, 0x2a, 0x00, 0x00, 0x00, //
    // ASM: ret
    0xc3,
];

/// The same shape in arm64 at 0x20000: a call to a local function, a
/// return, then the function, which sets x0 to 42.
const A64_CODE: &[u8] = &[
    // ASM: bl 0x20008 (from 0x20000)
    0x02, 0x00, 0x00, 0x94, //
    // ASM: ret
    0xc0, 0x03, 0x5f, 0xd6, //
    // ASM: mov x0, #42
    0x40, 0x05, 0x80, 0xd2, //
    // ASM: ret
    0xc0, 0x03, 0x5f, 0xd6,
];

/// Bytes of the dump's code part, padded with `int3`.
const DUMP_CODE_LEN: usize = 0x20;

/// A two-part dump: 0x20 bytes of code that loads a dword from 0x20000
/// and returns it, then 0x10 bytes of data whose first dword is 42.
///
/// # Returns
///
/// The dump's 0x30 bytes.
fn dump() -> Vec<u8> {
    let code: &[u8] = &[
        // ASM: mov eax, dword ptr [0x20000]
        0x8b, 0x04, 0x25, 0x00, 0x00, 0x02, 0x00, //
        // ASM: ret
        0xc3,
    ];
    let mut bytes = vec![0xcc; DUMP_CODE_LEN];
    bytes[..code.len()].copy_from_slice(code);
    bytes.extend_from_slice(&[42, 0, 0, 0]);
    bytes.resize(DUMP_CODE_LEN + 0x10, 0);
    bytes
}

/// The dump's regions: the code read-execute at 0x10000, the data
/// read-write at 0x20000.
const DUMP_REGIONS: &str = "0x10000@0:0x20:rx,0x20000@0x20:0x10:rw";

/// Maps bytes by a layout stated in words.
///
/// # Arguments
///
/// * `arch` - The architecture's word.
/// * `base` - `base`, when stated.
/// * `entry` - `entry`, when stated.
/// * `regions` - `regions`, when stated.
/// * `bytes` - The file.
///
/// # Returns
///
/// The program.
///
/// # Errors
///
/// The first refusal, as text with every cause.
fn map(
    arch: &str,
    base: Option<&str>,
    entry: Option<&str>,
    regions: Option<&str>,
    bytes: &[u8],
) -> Result<Program, String> {
    let arch = parse_arch(arch).map_err(|e| format!("{e:#}"))?;
    let layout = Layout::parse(Some(arch), base, entry, regions)
        .map_err(|e| format!("{e:#}"))?
        .expect("an arch states a layout");
    layout
        .program(PathBuf::from("blob.bin"), bytes.to_vec())
        .map_err(|e| format!("{e:#}"))
}

/// The error a layout is refused with.
///
/// # Arguments
///
/// * `regions` - The x86-64 regions stated.
/// * `bytes` - The file.
///
/// # Returns
///
/// The error's text, every cause included.
fn refused(regions: &str, bytes: &[u8]) -> String {
    map("x64", None, None, Some(regions), bytes).expect_err("the layout is refused")
}

/// x86-64 code loaded at a stated base is a program like any other.
///
/// Two functions are discovered, the first decompiles to the call plus
/// one, and the emulator runs it to 43. Two loads answer byte for byte
/// alike.
#[test]
fn x64_code_at_a_stated_base_discovers_decompiles_and_emulates() {
    let p = map("x64", Some("0x10000"), None, None, X64_CODE).expect("the layout maps");
    assert_eq!(p.format, BinaryFormat::Raw);
    assert_eq!(p.arch, Arch::X86_64);
    assert_eq!(
        p.entry,
        Some(0x10000),
        "the entry defaults to the first byte"
    );
    assert_eq!(p.image_base, 0x10000);
    let summary = p.summary();
    assert!(
        summary.contains("format:  raw   arch: x86-64 (64-bit)\n"),
        "{summary}"
    );
    assert!(summary.contains("kind stated layout"), "{summary}");
    assert!(!summary.contains("code:"), "{summary}");

    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert_eq!(entries, [0x10000, 0x1000b]);
    let text = decompiled(&p, 0x10000);
    assert!(text.contains("sub_1000b()"), "{text}");
    assert!(text.contains("+ 1"), "{text}");
    let ran = render::emulate_tsv(&p, &a, &Overlay::default(), "0x10000").expect("it runs");
    assert!(ran.contains("returned"), "{ran}");
    assert!(ran.contains("rax=0x2b "), "{ran}");

    let again = map("x64", Some("0x10000"), None, None, X64_CODE).expect("the layout maps");
    assert_eq!(again.summary(), summary);
    assert_eq!(
        render::emulate_tsv(
            &again,
            &Analysis::compute(&again),
            &Overlay::default(),
            "0x10000"
        ),
        Ok(ran)
    );
}

/// A stated entry replaces the first byte as the entry, and x86 code
/// maps at a 32-bit base as a 32-bit program.
#[test]
fn a_stated_entry_and_a_32_bit_arch_are_kept() {
    let p = map("x64", Some("0x10000"), Some("0x1000b"), None, X64_CODE).expect("it maps");
    assert_eq!(p.entry, Some(0x1000b));
    let x86 = map("x86", Some("0x400000"), None, None, &[0xc3]).expect("it maps");
    assert_eq!(x86.arch, Arch::X86);
    assert!(!x86.is_64);
    assert!(x86.summary().contains("arch: x86 (32-bit)"));
}

/// arm64 code maps as a 64-bit arm64 program that disassembles, with the
/// call's target read off the word; the stages arm64 does not have yet
/// say so instead of reading the bytes as x86.
#[test]
fn arm64_code_at_a_stated_base_disassembles() {
    let p = map("arm64", Some("0x20000"), None, None, A64_CODE).expect("it maps");
    assert_eq!(p.arch, Arch::Arm64);
    assert!(p.is_64);
    assert_eq!(p.isa_for(Feature::Disasm), Ok(Isa::A64));
    assert!(p.refuses(Feature::Decompile).is_some());
    let code = p.read_va_upto(0x20000, A64_CODE.len()).expect("mapped");
    let lines = disasm::disassemble_isa(code, 0x20000, Isa::A64, 4);
    assert_eq!(lines.len(), 4);
    assert_eq!(lines[0].text, "bl 0x20008");
    assert_eq!(lines[0].target, Some(0x20008));
    assert_eq!(lines[1].text, "ret");
    assert_eq!(lines[3].va, 0x2000c);
}

/// Two regions of one dump map at their own addresses: each section
/// reads its own file bytes, the code reads the data region, and the
/// entry and image base are the code region's.
#[test]
fn a_two_region_dump_maps_each_part_at_its_address() {
    let bytes = dump();
    let p = map("x64", None, None, Some(DUMP_REGIONS), &bytes).expect("it maps");
    let rows: Vec<(String, u64, u64, String)> = p
        .sections
        .iter()
        .map(|s| (s.name.clone(), s.va, s.file_off, s.perms()))
        .collect();
    assert_eq!(
        rows,
        [
            ("region0".to_owned(), 0x10000, 0, "r-x".to_owned()),
            ("region1".to_owned(), 0x20000, 0x20, "rw-".to_owned()),
        ]
    );
    assert_eq!(p.entry, Some(0x10000));
    assert_eq!(p.image_base, 0x10000);
    assert_eq!(p.read_va(0x20000, 4), Some(&[42u8, 0, 0, 0][..]));
    assert_eq!(p.va_to_offset(0x20004), Some(0x24));
    assert_eq!(p.read_va(0x10020, 1), None, "the gap is unmapped");

    let a = Analysis::compute(&p);
    let ran = render::emulate_tsv(&p, &a, &Overlay::default(), "0x10000").expect("it runs");
    assert!(ran.contains("rax=0x2a "), "{ran}");
    let text = decompiled(&p, 0x10000);
    assert!(text.contains("20000"), "{text}");

    let reversed = map(
        "x64",
        None,
        None,
        Some("0x20000@0x20:0x10:rw,0x10000@0:0x20:rx"),
        &bytes,
    )
    .expect("it maps");
    assert_eq!(reversed.entry, Some(0x10000), "the first executable region");
    assert_eq!(reversed.image_base, 0x10000, "the lowest region");
    assert_eq!(reversed.sections[0].name, "region0");
    assert_eq!(reversed.sections[0].va, 0x20000, "named in stated order");
}

/// A file whose first bytes name a container still maps raw when a
/// layout is stated, and the summary warns that its headers went unread.
#[test]
fn a_container_mapped_raw_is_warned_about() {
    let p = map("x64", None, None, None, b"MZ\x90\x00\xc3").expect("it maps");
    let summary = p.summary();
    assert!(
        summary.contains("# warning: the file starts like a PE; mapped as raw bytes"),
        "{summary}"
    );
}

/// No arch and nothing else stated is no layout, so the file's own
/// headers are read as before; base, entry or regions without arch are
/// refused rather than ignored.
#[test]
fn without_arch_there_is_no_layout() {
    assert_eq!(Layout::parse(None, None, None, None).ok(), Some(None));
    for (base, entry, regions) in [
        (Some("0x1000"), None, None),
        (None, Some("0x1000"), None),
        (None, None, Some("0@0:1")),
    ] {
        let err = Layout::parse(None, base, entry, regions).expect_err("refused");
        assert!(format!("{err}").contains("need arch"), "{err}");
    }
    let unknown = Layout::parse(Some(Arch::Unknown), None, None, None).expect_err("refused");
    assert!(
        format!("{unknown}").contains("names no instruction set"),
        "{unknown}"
    );
    assert!(parse_arch("mips").is_err());
    assert_eq!(parse_arch("AMD64").ok(), Some(Arch::X86_64));
    assert_eq!(parse_arch("aarch64").ok(), Some(Arch::Arm64));
}

/// Every number a layout states is checked against the file and the
/// address space.
///
/// Each refusal names the region and its numbers: a region past the end
/// of the file, an offset or address that overflows, a zero length, an
/// overlap, an x86 address past 4 GiB, an entry outside the regions or in
/// data, and malformed text.
#[test]
fn hostile_layouts_are_refused_with_their_numbers() {
    let bytes = dump();
    let cases: &[(&str, &str)] = &[
        (
            "0x10000@0x20:0x20",
            "region 0 (offset 0x20, length 0x20) runs past the end of the file at 0x30",
        ),
        (
            "0x10000@0xffffffffffffffff:2",
            "runs past the end of the file",
        ),
        (
            "0xffffffffffffffff@0:0x10",
            "region 0 at 0xffffffffffffffff with 0x10 bytes runs past the top of the x86-64 address space",
        ),
        ("0x10000@0:0", "length 0: a region maps at least one byte"),
        (
            "0x10000@0:0x20,0x1001f@0x20:0x10",
            "region 0 (0x10000..0x10020) and region 1 (0x1001f..0x1002f) overlap",
        ),
        ("0x10000@0x10", "expected VA@OFF:LEN[:PERMS]"),
        ("0x10000@0:0x10:0x10:rx", "expected VA@OFF:LEN[:PERMS]"),
        ("", "region 0 ''"),
        ("0x10000@0:0x20:rwq", "'q' is none of r, w and x"),
        ("0x10000@0:0x20:rr", "'r' given twice"),
        ("0x10000@0:0x20:-", "name at least one of r, w and x"),
        (
            "0x1ffffffffffffffff@0:1",
            "address '0x1ffffffffffffffff': not a number that fits 64 bits",
        ),
        ("0x10000@zero:1", "offset 'zero': not a number"),
    ];
    for (regions, said) in cases {
        let err = refused(regions, &bytes);
        assert!(err.contains(said), "{regions}: {err}");
    }

    let too_many = vec!["0@0:1"; REGIONS_MAX + 1].join(",");
    let err = refused(&too_many, &bytes);
    assert!(err.contains("257 regions stated; at most 256"), "{err}");

    let x86 = map("x86", Some("0xfffffff0"), None, None, &bytes).expect_err("refused");
    assert!(
        x86.contains("past the top of the x86 address space"),
        "{x86}"
    );
    let outside =
        map("x64", None, Some("0x30000"), Some(DUMP_REGIONS), &bytes).expect_err("refused");
    assert!(
        outside.contains(
            "entry 0x30000 is in no mapped region; mapped: 0x10000..0x10020 0x20000..0x20010"
        ),
        "{outside}"
    );
    let ten = (0..10)
        .map(|i| format!("{:#x}@{i}:1", 0x10 * i))
        .collect::<Vec<_>>()
        .join(",");
    let listed = map("x64", None, Some("0x1000"), Some(&ten), &bytes).expect_err("refused");
    assert!(listed.ends_with("0x70..0x71 ... 2 more"), "{listed}");
    let data = map("x64", None, Some("0x20000"), Some(DUMP_REGIONS), &bytes).expect_err("refused");
    assert!(data.contains("region 1, which is not executable"), "{data}");
    let both =
        Layout::parse(Some(Arch::X86_64), Some("0"), None, Some("0@0:1")).expect_err("refused");
    assert!(format!("{both}").contains("give one"), "{both}");
    let empty = map("x64", None, None, None, &[]).expect_err("refused");
    assert!(empty.contains("the file is empty"), "{empty}");
}
