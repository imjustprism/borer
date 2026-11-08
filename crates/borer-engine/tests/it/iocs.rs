//! `borer://iocs` over hand-built images.
//!
//! The indicators read out of planted strings with their provenance, the
//! negatives a matcher must reject, and the caveats triage states about
//! what it could not see.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::iocs_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::ioc::{Kind, classify};
use borer_engine::program::{Arch, Program, Section};

/// A raw x64 image whose read-only data holds planted strings: real
/// indicators of several kinds, and negatives a matcher must reject.
fn planted() -> Program {
    const STRINGS: &[&str] = &[
        "http://evil.example.com/gate.php",
        "connect c2.badhost.ru now",
        "45.33.12.9",
        "HKEY_CURRENT_USER\\Software\\Demo\\Run",
        "\\\\.\\pipe\\demo_channel",
        "admin@mail.example.org",
        "demo version 1.2.3.4 build",
        "see http:// for details",
        "lib/core/src/main.rs",
        "System.Net.Sockets.Socket",
        "127.0.0.1",
    ];
    let mut bytes = vec![0u8; 0x3000];
    let mut at = 0x2000usize;
    for s in STRINGS {
        bytes[at..at + s.len()].copy_from_slice(s.as_bytes());
        at += s.len() + 1;
    }
    let b64 = "aHR0cHM6Ly9iNjQuZXhhbXBsZS5uZXQveA==";
    bytes[at..at + b64.len()].copy_from_slice(b64.as_bytes());
    bytes[0x1000] = 0xc3; // ASM: ret
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    )
}

/// Each planted indicator is listed with its kind, and the base64 one is
/// decoded, each row carrying its source and the string's address.
#[test]
fn planted_indicators_are_classified_with_provenance() {
    let p = planted();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = iocs_tsv(&p, &a, &o, "").expect("iocs");
    for value in [
        "http://evil.example.com/gate.php",
        "c2.badhost.ru",
        "45.33.12.9",
        "HKEY_CURRENT_USER\\Software\\Demo\\Run",
        "\\\\.\\pipe\\demo_channel",
        "admin@mail.example.org",
    ] {
        assert!(out.contains(value), "missing {value}: {out}");
    }
    assert!(out.contains("https://b64.example.net/x"), "base64: {out}");
    assert!(out.contains("decoded-b64"), "{out}");
    assert!(
        out.lines()
            .any(|l| l.contains("url") && l.contains("static")),
        "{out}"
    );
}

/// The negatives are not indicators, and the loopback address is kept but
/// marked benign.
#[test]
fn negatives_are_rejected_and_the_common_marked_benign() {
    let p = planted();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = iocs_tsv(&p, &a, &o, "").expect("iocs");
    assert!(!out.contains("1.2.3.4"), "a version is an address: {out}");
    assert!(!out.contains("main.rs"), "a source path is a domain: {out}");
    assert!(
        !out.contains("System.Net.Sockets"),
        "a scoped name is a domain: {out}"
    );
    assert!(out.contains("127.0.0.1"), "the loopback is dropped: {out}");
    assert!(
        out.lines()
            .any(|l| l.contains("127.0.0.1") && l.contains("benign-common")),
        "the loopback is not benign: {out}"
    );
    assert!(classify("demo version 1.2.3.4 build").is_empty());
    assert!(classify("see http:// for details").is_empty());
}

/// A string a function builds on its stack is an indicator tagged `stack`,
/// at the store that starts it.
#[test]
fn a_stack_built_string_is_tagged_stack() {
    // ASM: a function writing "evil.ru\0" one dword at a time onto the
    // stack: `mov dword [rsp-8], "evil"; mov dword [rsp-4], ".ru\0"; ret`.
    let code: &[u8] = &[
        0xc7, 0x44, 0x24, 0xf8, 0x65, 0x76, 0x69, 0x6c, // ASM: mov dword [rsp-8],0x6c697665
        0xc7, 0x44, 0x24, 0xfc, 0x2e, 0x72, 0x75, 0x00, // ASM: mov dword [rsp-4],0x0075722e
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0xccu8; 0x2000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    p.function_ranges = vec![(0x1000, 0x1011)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = iocs_tsv(&p, &a, &o, "domain").expect("iocs");
    assert!(
        out.lines()
            .any(|l| l.contains("evil.ru") && l.contains("stack")),
        "{out}"
    );
}

/// A kind filter keeps only its kind, and the listing is deterministic.
#[test]
fn a_filter_narrows_and_the_listing_is_deterministic() {
    let p = planted();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let urls = iocs_tsv(&p, &a, &o, "url").expect("iocs");
    assert!(urls.contains("http://evil.example.com/gate.php"), "{urls}");
    assert!(!urls.contains("45.33.12.9"), "{urls}");
    let first = iocs_tsv(&p, &a, &o, "").expect("iocs");
    let second = iocs_tsv(&p, &a, &o, "").expect("iocs");
    assert_eq!(first, second);
    let mut plain_bytes = vec![0xccu8; 0x1000];
    plain_bytes[0] = 0xc3; // ASM: ret
    let plain = Program::raw(
        plain_bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    let pa = Analysis::compute(&plain);
    let plain_out = iocs_tsv(&plain, &pa, &o, "").expect("iocs");
    assert!(plain_out.starts_with("# 0 indicators"), "{plain_out}");
}

/// The classifier reads each kind from the text that spells it (a unit
/// check that does not need an image).
#[test]
fn the_classifier_reads_each_kind() {
    let kind = |text: &str| classify(text).first().map(|i| i.kind);
    assert_eq!(kind("http://host.example.com/a"), Some(Kind::Url));
    assert_eq!(kind("sub.example.io"), Some(Kind::Domain));
    assert_eq!(kind("203.0.113.7"), Some(Kind::Ipv4));
    assert_eq!(kind("HKLM\\Software\\X"), Some(Kind::Registry));
    assert_eq!(kind("\\\\.\\pipe\\x"), Some(Kind::Pipe));
    assert_eq!(kind("C:\\Windows\\x.exe"), Some(Kind::Path));
}

/// An indicator is as sure as where its bytes sit.
///
/// A URL a function references counts, while one in data nothing
/// references, or in bytes appended past the image, reads low with its
/// region named and is counted apart, so planted URLs do not raise the
/// indicators the listing calls ones to act on.
#[test]
fn an_indicator_no_code_references_reads_low_and_apart() {
    use crate::elfgen::{self, A, AX, EM_X86_64, ET_EXEC, PROGBITS, Sec};
    let mut rodata = b"http://gate.badhost.ru/a.php\0".to_vec();
    rodata.extend_from_slice(b"http://idle.badhost.ru/b.php\0");
    rodata.extend_from_slice(b"GET /a HTTP/1.1\r\nhttp://line.badhost.ru/c.php\r\n\0");
    rodata.resize(0x70, 0);
    for unit in "GET /w\r\nhttp://wide.badhost.ru/d.php\r\n\0".encode_utf16() {
        rodata.extend_from_slice(&unit.to_le_bytes());
    }
    rodata.resize(0xc0, 0);
    rodata.extend_from_slice(b"AAAAAAAA");
    for unit in "\r\nhttp://tail.badhost.ru/e.php\0".encode_utf16() {
        rodata.extend_from_slice(&unit.to_le_bytes());
    }
    let code = vec![
        0x48, 0x8d, 0x3d, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rdi,[rip+0xff9]
        0x48, 0x8d, 0x35, 0x2c, 0x10, 0x00, 0x00, // ASM: lea rsi,[rip+0x102c]
        0x48, 0x8d, 0x15, 0x5b, 0x10, 0x00, 0x00, // ASM: lea rdx,[rip+0x105b]
        0x48, 0x8d, 0x0d, 0xa4, 0x10, 0x00, 0x00, // ASM: lea rcx,[rip+0x10a4]
        0xc3, // ASM: ret
    ];
    let mut bytes = elfgen::build(
        ET_EXEC,
        EM_X86_64,
        0x1000,
        &[
            Sec::new(".text", PROGBITS, AX, 0x1000, code),
            Sec::new(".rodata", PROGBITS, A, 0x2000, rodata),
        ],
    );
    let appended = bytes.len() + 1;
    bytes.extend_from_slice(b"\0http://decoy.badhost.ru/c.php\0");
    let p = Program::from_bytes(std::path::PathBuf::from("iocs.elf"), bytes).expect("loads");
    let a = Analysis::compute(&p);
    let out = iocs_tsv(&p, &a, &Overlay::default(), "url").expect("iocs");
    assert!(
        out.lines()
            .next()
            .is_some_and(|l| l.ends_with(": 3 url (+3 no code references)")),
        "{out}"
    );
    let row = |host: &str| -> Vec<String> {
        out.lines()
            .find(|l| l.contains(host))
            .map(|l| l.split_whitespace().map(str::to_owned).collect())
            .unwrap_or_default()
    };
    let gate = row("gate.badhost.ru");
    assert_eq!(
        gate[..5],
        ["url", "high", "static", "0x2000", "referenced"],
        "{out}"
    );
    assert_ne!(gate[5], "-", "{out}");
    for (host, site) in [("line.badhost.ru", "0x204b"), ("wide.badhost.ru", "0x2080")] {
        let line = row(host);
        assert_eq!(
            line[..6],
            [
                "url",
                "high",
                "static",
                site,
                "referenced",
                gate[5].as_str()
            ],
            "a URL on a later line of a literal its function references: {out}"
        );
    }
    let idle = row("idle.badhost.ru");
    assert_eq!(
        idle[..5],
        ["url", "low", "static", "0x201d", "unreferenced"],
        "{out}"
    );
    let tail = row("tail.badhost.ru");
    assert_eq!(
        tail[..5],
        ["url", "low", "static", "0x20cc", "unreferenced"],
        "a wide run is no line of the narrow string before it: {out}"
    );
    let decoy = row("decoy.badhost.ru");
    let site = format!("off={appended:#x}");
    assert_eq!(
        decoy[..5],
        ["url", "low", "static", site.as_str(), "appended"],
        "{out}"
    );
}
/// The walk back to a literal's start stays inside the run's section.
///
/// A URL whose section opens with a line break right after printable code
/// bytes is still the referenced literal it is, not code, and a run in
/// bytes no section maps is its own start, never a line of the referenced
/// string the image ends with.
#[test]
fn a_literal_walk_stays_inside_its_section() {
    let mut bytes = vec![
        0x48, 0x8d, 0x3d, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rdi,[rip+0xff9]
        0x48, 0x8d, 0x35, 0x10, 0x10, 0x00, 0x00, // ASM: lea rsi,[rip+0x1010]
        0xc3, // ASM: ret
    ];
    bytes.resize(0x18, 0);
    bytes.extend_from_slice(b"AAAAAAAA\nhttp://edge.badhost.ru/f.php\0BBBBBBBB");
    bytes.extend_from_slice(b"\nhttp://trail.badhost.ru/g.php\0");
    let sections = vec![
        Section::mapped(".text", 0x1000, 0, 0x20, false, true),
        Section::mapped(".data", 0x2000, 0x20, 0x26, false, false),
    ];
    let p = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), sections);
    let a = Analysis::compute(&p);
    let out = iocs_tsv(&p, &a, &Overlay::default(), "url").expect("iocs");
    assert!(
        out.lines()
            .next()
            .is_some_and(|l| l.ends_with(": 1 url (+1 no code references)")),
        "{out}"
    );
    let row = |host: &str| -> Vec<String> {
        out.lines()
            .find(|l| l.contains(host))
            .map(|l| l.split_whitespace().map(str::to_owned).collect())
            .unwrap_or_default()
    };
    assert_eq!(
        row("edge.badhost.ru")[..5],
        ["url", "high", "static", "0x2001", "referenced"],
        "{out}"
    );
    assert_eq!(
        row("trail.badhost.ru")[..5],
        ["url", "low", "static", "off=0x47", "unmapped"],
        "{out}"
    );
}
