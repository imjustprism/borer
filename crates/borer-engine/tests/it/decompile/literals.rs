//! Long string literals: an ordinary one stays cut at the 120 characters a
//! literal shows, marked `...`; only a signature prints whole. Short ones:
//! a code pointer is not a literal.

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::literal_at;
use borer_engine::program::{Arch, Program, Section};

/// Where [`holding`] places its text.
const AT: u64 = 0x2000;

/// Returns an image whose read-only data at [`AT`] holds `text`, then
/// zeros to the end of its two pages.
///
/// # Arguments
///
/// * `text` - The string's bytes, without their terminator, under 8 KiB.
fn holding(text: &str) -> Program {
    let mut bytes = text.as_bytes().to_vec();
    bytes.resize(0x2000, 0);
    let rdata = Section::mapped(".rdata", AT, 0, 0x2000, false, false);
    Program::raw(bytes, Arch::X86_64, 0, None, vec![rdata])
}

/// Returns how `text` prints where a function references it.
///
/// # Arguments
///
/// * `text` - The string's bytes, without their terminator.
fn shown(text: &str) -> String {
    let p = holding(text);
    literal_at(&p, &Analysis::compute(&p), AT, "sub_1000").unwrap_or_default()
}

/// Asserts `text` prints cut: at most 120 characters of it, then `...`.
///
/// # Arguments
///
/// * `text` - The string's bytes, longer than 120.
fn assert_cut(text: &str) {
    let shown = shown(text);
    assert!(shown.ends_with("...\""), "{shown}");
    assert!(shown.chars().count() < 140, "{shown}");
}

/// A long log message, an HTML blob, a multi-line text and prose naming
/// template bindings stay cut, however long: only a signature's text is
/// the answer, not a name.
#[test]
fn an_ordinary_long_literal_stays_cut() {
    let log = format!(
        "Connection to the update server failed, retrying later: {}",
        "the remote host closed the stream before the handshake ended; ".repeat(11)
    );
    assert!(log.len() >= 700);
    let html = format!(
        "<html><head><title>Error</title></head><body>{}</body></html>",
        "<p class=\"msg\">Something went wrong.</p>".repeat(10)
    );
    let lines = "Usage: tool [options] <file>\n  -v  verbose\n  -q  quiet\n".repeat(6);
    let prose = format!(
        "For the bindings a template reports, see [with T = int] {}",
        "and the notes on instantiation in the manual ".repeat(5)
    );
    for text in [log, html, lines, prose] {
        assert_cut(&text);
    }
}

/// Prose spelled as a signature, a message on a qualified name with a
/// long argument or bracketed details, stays cut.
///
/// Its words before the name read as a return type, and the message
/// printed whole, about 700 characters, at every reference.
#[test]
fn prose_shaped_as_a_signature_stays_cut() {
    let open = format!(
        "Fatal error in Net::Session::Open({})",
        "the remote host refused the session and no retry was left ".repeat(11)
    );
    let details = format!(
        "Error in Foo::Bar() [details = {}]",
        "the request carried no token ".repeat(17)
    );
    for text in [open, details] {
        assert!(text.len() > 500);
        assert_cut(&text);
    }
}

/// A template signature over 300 bytes prints whole, escaped as any
/// literal is.
#[test]
fn a_long_template_signature_prints_whole() {
    let sig = format!(
        "void Box<T>::Put(const T&) [with T = std::map<std::__cxx11::basic_string<char>, {}>]",
        "std::vector<Widget*, std::allocator<Widget*> >".repeat(6)
    );
    assert!(sig.len() > 300);
    assert_eq!(shown(&sig), format!("\"{sig}\""));
}

/// A signature run past the bytes a string scan reads is marked cut,
/// even when the last byte read closes its bindings.
///
/// The scan stopped on the `]` at byte 4096 of a 5000-byte run, and the
/// run printed as a complete literal.
#[test]
fn a_signature_past_the_scan_is_marked_cut() {
    let head = "void A<T>::f() [with T = ";
    let sig = format!(
        "{head}{}]{}",
        "x".repeat(4095 - head.len()),
        "y".repeat(904)
    );
    assert_eq!(sig.len(), 5000);
    assert!(shown(&sig).ends_with("...\""), "{}", shown(&sig));
}

/// Two read-only words holding one code pointer print as two addresses,
/// not as the string their low bytes spell.
///
/// The pointer 0x140002760 is the bytes `60 27 00 40 01 00 00 00`, which
/// read as `` "`'" ``: notepad stored two vtable slots that way and both
/// printed as that one literal.
#[test]
fn a_word_pointing_into_code_is_not_a_short_literal() {
    let code: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x1f, 0x00, 0x00, // ASM: lea rax, [rip+0x1ff9] (0x140003000)
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0x48, 0x8d, 0x05, 0xf7, 0x1f, 0x00, 0x00, // ASM: lea rax, [rip+0x1ff7] (0x140003008)
        0x48, 0x89, 0x41, 0x08, // ASM: mov [rcx+8], rax
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0u8; 0x3000];
    bytes[..code.len()].copy_from_slice(code);
    let slot = 0x1_4000_2760u64.to_le_bytes();
    bytes[0x2000..0x2008].copy_from_slice(&slot);
    bytes[0x2008..0x2010].copy_from_slice(&slot);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![
            Section::mapped(".text", 0x1_4000_1000, 0, 0x2000, false, true),
            Section::mapped(".rdata", 0x1_4000_3000, 0x2000, 0x1000, false, false),
        ],
    );
    let text = crate::decompiled::decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("\"`'\""), "{text}");
    assert!(
        text.contains("140003000") && text.contains("140003008"),
        "{text}"
    );
}

/// A 32-bit image keeps the strings whose first four bytes happen to read
/// as an address in its code.
///
/// The words are the literals' own bytes: `L"HARDWARE\\DESCRIPTION\\System"`
/// is 0x00410048, `L"VBOX"` 0x00420056 and `"N/A"` 0x00412f4e, all inside
/// `.text`. 0x420056 is also the entry point, a discovered function: the
/// wide reading is tried first and wins, so `L"VBOX"` still prints; only a
/// one to three character narrow reading gives way to an entry.
#[test]
fn a_32_bit_string_reading_as_a_code_address_stays_a_literal() {
    let mut bytes = vec![0u8; 0x21000];
    bytes[0x1f056] = 0xc3; // ASM: ret
    let wide = |s: &str| -> Vec<u8> { s.encode_utf16().flat_map(u16::to_le_bytes).collect() };
    let hardware = wide("HARDWARE\\DESCRIPTION\\System");
    bytes[0x20100..0x20100 + hardware.len()].copy_from_slice(&hardware);
    let vbox = wide("VBOX");
    bytes[0x20200..0x20200 + vbox.len()].copy_from_slice(&vbox);
    bytes[0x20300..0x20303].copy_from_slice(b"N/A");
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0x40_0000,
        Some(0x42_0056),
        vec![
            Section::mapped(".text", 0x40_1000, 0, 0x2_0000, false, true),
            Section::mapped(".rdata", 0x42_1000, 0x2_0000, 0x1000, false, false),
        ],
    );
    p.format = borer_engine::program::BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    assert!(a.function(0x42_0056).is_some(), "the entry is no function");
    assert!(a.function(0x41_2f4e).is_none(), "N/A's word is an entry");
    let at = |va| literal_at(&p, &a, va, "sub_401000");
    assert_eq!(
        at(0x42_1100).as_deref(),
        Some("L\"HARDWARE\\\\DESCRIPTION\\\\System\"")
    );
    assert_eq!(at(0x42_1200).as_deref(), Some("L\"VBOX\""));
    assert_eq!(at(0x42_1300).as_deref(), Some("\"N/A\""));
}
