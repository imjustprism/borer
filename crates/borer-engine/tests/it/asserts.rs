//! What a build that keeps its assertions says: the next steps a function
//! that asserts points at.
//!
//! The image is a stripped build with assertions on, the shape GitHub issue
//! 24's binary has: every method guards one member and reports a failure
//! as `assert("<expression>", "<file>", <line>, "<__PRETTY_FUNCTION__>")`,
//! the signature literal naming the method, and nothing else names it.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::answer_header;
use borer_engine::analysis::render::{NEXT_MAX, function_summary, next_steps};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::{from_usize, lo32, saturating_usize};
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

/// The import slot the assert reporter is called through.
const IAT: u64 = 0x2000;

/// The source file every assert cites.
const PATH: u64 = 0x2100;

/// `"this->m_name"`.
const NAME: u64 = 0x2120;

/// `"this->m_size > 0"`.
const SIZE: u64 = 0x2140;

/// `"this->m_flags < this->m_limit"`, two members in one expression.
const FLAGS: u64 = 0x2160;

/// `"count > 0"`, which names no member.
const COUNT: u64 = 0x2180;

/// `"this->m_id"`.
const ID: u64 = 0x2190;

/// `"this->m_key"`, asserted at the offset `m_id` is.
const KEY: u64 = 0x21a0;

/// `"this->IsReady()"`, a getter.
const READY: u64 = 0x21b0;

/// `"this->m_depth"`, asserted over a field of what a field points at.
const DEPTH: u64 = 0x21c0;

/// `"this->m_rect.w > 0"`, a member reached into.
const RECT: u64 = 0x2700;

/// `"this->m_key == \"\" || this->m_val"`, two members around a quoted
/// empty string.
const QUOTE: u64 = 0x2720;

/// A condition whose member is spelled past its 160th character.
const FAR: u64 = 0x2760;

/// Where [`PRETTY`] sits.
const LONG: u64 = 0x2400;

/// The `__PRETTY_FUNCTION__` GCC writes for a method of a class
/// template, 292 characters: its arguments come last, after the
/// decompiler's 120 and the read's 200.
const PRETTY: &str = "void Box<T>::Put(const T&) [with T = std::map<std::__cxx11::basic_string<char>, std::vector<Widget*, std::allocator<Widget*> >, std::less<std::__cxx11::basic_string<char> >, std::allocator<std::pair<const std::__cxx11::basic_string<char>, std::vector<Widget*, std::allocator<Widget*> > > > >]";

/// What a method's guard reads before it reports.
#[derive(Clone, Copy)]
enum Guard {
    /// The field at the offset of `this`: `mov eax, [rcx+off]`.
    Field(u32),
    /// The field at 8 of what the field at the offset points at: `mov
    /// rax, [rcx+off]; mov eax, [rax+8]`.
    Behind(u32),
}

/// The methods: entry, what its guard reads, the expression its assert
/// reports, and the `__PRETTY_FUNCTION__` naming it with where that sits.
const METHODS: [(u64, Guard, u64, u64, &str); 18] = [
    (
        0x1100,
        Guard::Field(0x270),
        NAME,
        0x2200,
        "void Widget::SetName()",
    ),
    (
        0x1140,
        Guard::Field(0x270),
        NAME,
        0x2240,
        "void Widget::Rename()",
    ),
    (
        0x1180,
        Guard::Field(0x10),
        SIZE,
        0x2280,
        "void Widget::Grow()",
    ),
    (
        0x11c0,
        Guard::Field(0x18),
        SIZE,
        0x22c0,
        "void Widget::Shrink()",
    ),
    (
        0x1200,
        Guard::Field(0x30),
        FLAGS,
        0x2300,
        "void Widget::Swap()",
    ),
    (0x1240, Guard::Field(0x8), COUNT, LONG, PRETTY),
    (0x1280, Guard::Field(0x40), ID, 0x2340, "void Widget::Tag()"),
    (
        0x12c0,
        Guard::Field(0x40),
        ID,
        0x2380,
        "void Widget::Retag()",
    ),
    (
        0x1300,
        Guard::Field(0x40),
        KEY,
        0x23c0,
        "void Widget::Key()",
    ),
    (
        0x1340,
        Guard::Field(0x50),
        READY,
        0x2600,
        "void Widget::Ready()",
    ),
    (
        0x1380,
        Guard::Field(0x50),
        READY,
        0x2640,
        "void Widget::Wait()",
    ),
    (
        0x13c0,
        Guard::Behind(0x48),
        DEPTH,
        0x2680,
        "void Widget::Deep()",
    ),
    (
        0x1400,
        Guard::Behind(0x48),
        DEPTH,
        0x26c0,
        "void Widget::Deeper()",
    ),
    (
        0x1440,
        Guard::Field(0x48),
        RECT,
        0x2840,
        "void Widget::Fit()",
    ),
    (
        0x1480,
        Guard::Field(0x48),
        RECT,
        0x2880,
        "void Widget::Refit()",
    ),
    (
        0x14c0,
        Guard::Field(0x58),
        QUOTE,
        0x28c0,
        "void Widget::Look()",
    ),
    (
        0x1500,
        Guard::Field(0x58),
        QUOTE,
        0x2900,
        "void Widget::Relook()",
    ),
    (
        0x1540,
        Guard::Field(0x60),
        FAR,
        0x2940,
        "void Widget::Far()",
    ),
];

/// Returns an instruction at `at` whose last four bytes are the
/// displacement from its end to `to`.
///
/// # Arguments
///
/// * `at` - Where the instruction starts.
/// * `op` - Its bytes before the displacement.
/// * `to` - The address it reaches.
fn rip(at: u64, op: &[u8], to: u64) -> Vec<u8> {
    let end = at + from_usize(op.len()) + 4;
    [op, &lo32(to.wrapping_sub(end)).to_le_bytes()].concat()
}

/// Returns a method at `at` that reports a failed assert when what its guard
/// reads is zero.
///
/// It holds the guard's load into `eax`, then `test eax, eax; jnz R; lea rcx,
/// [expr]; lea rdx, [PATH]; mov r8d, line; lea r9, [sig]; call [IAT]; R: ret`.
///
/// # Arguments
///
/// * `at` - The method's entry.
/// * `guard` - What the guard reads.
/// * `expr` - The asserted expression's address.
/// * `line` - The line the assert reports.
/// * `sig` - The signature literal's address.
fn guarded_assert(at: u64, guard: Guard, expr: u64, line: u32, sig: u64) -> Vec<u8> {
    let mut code = match guard {
        Guard::Field(off) => [&[0x8b, 0x81][..], &off.to_le_bytes()].concat(), // ASM: mov eax, [rcx+off32]
        Guard::Behind(off) => [
            &[0x48, 0x8b, 0x81][..],
            &off.to_le_bytes(),
            &[0x8b, 0x40, 0x08],
        ]
        .concat(), // ASM: mov rax, [rcx+off32]; mov eax, [rax+8]
    };
    let body = at + from_usize(code.len()) + 4;
    code.extend_from_slice(&[0x85, 0xc0, 0x75, 0x21]); // ASM: test eax, eax; jnz +0x21 (the ret)
    code.extend(rip(body, &[0x48, 0x8d, 0x0d], expr)); // ASM: lea rcx, [rip+expr]
    code.extend(rip(body + 7, &[0x48, 0x8d, 0x15], PATH)); // ASM: lea rdx, [rip+path]
    code.extend_from_slice(&[0x41, 0xb8]); // ASM: mov r8d, imm32
    code.extend_from_slice(&line.to_le_bytes());
    code.extend(rip(body + 20, &[0x4c, 0x8d, 0x0d], sig)); // ASM: lea r9, [rip+sig]
    code.extend(rip(body + 27, &[0xff, 0x15], IAT)); // ASM: call qword [rip+iat]
    code.push(0xc3); // ASM: ret
    code
}

/// Builds the image.
///
/// It places `.text` at 0x1000, entered at a `main` that calls each of
/// [`METHODS`], and a read-only `.rdata` at 0x2000 holding the reporter's
/// import slot, the path, the expressions and the signatures.
fn widget() -> Program {
    let mut bytes = vec![0xccu8; 0x1000];
    bytes.resize(0x2000, 0);
    let mut put = |va: u64, b: &[u8]| {
        let off = saturating_usize(va - 0x1000);
        bytes[off..off + b.len()].copy_from_slice(b);
    };
    let mut main = Vec::new();
    for (k, &(entry, guard, expr, sig_at, sig)) in (0u64..).zip(&METHODS) {
        main.extend(rip(0x1000 + 5 * k, &[0xe8], entry)); // ASM: call method
        put(sig_at, &[sig.as_bytes(), &[0]].concat());
        put(
            entry,
            &guarded_assert(entry, guard, expr, 12 + lo32(k), sig_at),
        );
    }
    main.push(0xc3); // ASM: ret
    put(0x1000, &main);
    put(PATH, b"src/widget.cpp\0");
    put(NAME, b"this->m_name\0");
    put(SIZE, b"this->m_size > 0\0");
    put(FLAGS, b"this->m_flags < this->m_limit\0");
    put(COUNT, b"count > 0\0");
    put(ID, b"this->m_id\0");
    put(KEY, b"this->m_key\0");
    put(READY, b"this->IsReady()\0");
    put(DEPTH, b"this->m_depth\0");
    put(RECT, b"this->m_rect.w > 0\0");
    put(QUOTE, b"this->m_key == \"\" || this->m_val\0");
    put(
        FAR,
        &[&*b"1 == 1 && ".repeat(16), b"this->m_far\0"].concat(),
    );
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols.push(Symbol {
        name: "KERNEL32.dll!ReportAssertFailure".to_owned(),
        addr: IAT,
        kind: SymbolKind::Import,
    });
    p
}

/// A method whose text shows an assert points at the members its class's
/// asserts name and at the source file they cite.
///
/// It does so in its decompile header and at the end of its summary; a function
/// that asserts nothing does not.
///
/// An agent working on issue 24's binary wrote this pairing by hand while
/// `borer://asserts` and `borer://sources` were there to be read: the
/// pointer has to be where the assert is seen.
#[test]
fn an_assert_points_at_the_asserts_and_the_sources() {
    let p = widget();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let step = "borer://asserts/Widget (the members its class's asserts name), borer://sources/widget.cpp (the source file they cite)";
    let steps = next_steps(&p, &a, &o, 0x1100);
    assert!(steps.iter().any(|s| s == step), "{steps:?}");
    assert!(steps.len() <= NEXT_MAX, "{steps:?}");
    let header = answer_header(&p, &a, &o, 0x1100, None).unwrap_or_default();
    assert!(header.contains(&format!("// next: {step}")), "{header}");
    let summary = function_summary(&p, &a, &o, 0x1100).expect("a function");
    assert!(summary.ends_with(&format!("# next: {step}\n")), "{summary}");
    let main = next_steps(&p, &a, &o, 0x1000);
    assert!(
        main.iter().all(|s| !s.contains("borer://asserts")),
        "{main:?}"
    );
}
