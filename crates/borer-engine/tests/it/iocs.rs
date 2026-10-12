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
        // Negatives: a version, a truncated URL, a source path's extension,
        // a scoped identifier, the loopback address (kept, marked benign).
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
    // A base64 string whose plaintext is a URL, decoded by the second pass.
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
    // The bare matcher agrees on the hardest negatives.
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
    // The indicators of a plain image with no planted text are none.
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
