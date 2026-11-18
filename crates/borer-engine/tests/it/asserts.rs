//! What a build that keeps its assertions says.
//!
//! It covers the next steps a function that asserts points at, and each member
//! its asserts spell paired with the field offset the code around them reads,
//! a long `__PRETTY_FUNCTION__` read whole in parts, and template
//! signatures shown whole without naming anything.
//!
//! The image is a stripped build with assertions on, the shape GitHub issue
//! 24's binary has: every method guards one member and reports a failure
//! as `assert("<expression>", "<file>", <line>, "<__PRETTY_FUNCTION__>")`,
//! the signature literal naming the method, and nothing else names it.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::classes::field_names;
use borer_engine::analysis::decompile::{answer_header, decompile, skeleton};
use borer_engine::analysis::protos::Proto;
use borer_engine::analysis::render::{NEXT_MAX, asserted_fields_tsv, function_summary, next_steps};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::memory::{Kind, read_values, rest_of_cut};
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

/// Builds an image of methods that assert.
///
/// It places `.text` at 0x1000, entered at a `main` that calls each of
/// `methods`, and a read-only `.rdata` at 0x2000 holding the reporter's
/// import slot, the path, the expressions and the signatures.
///
/// # Arguments
///
/// * `methods` - Entry, guard, expression, signature address and
///   signature of each method.
/// * `texts` - Each expression's address and its terminated bytes.
fn image(methods: &[(u64, Guard, u64, u64, &str)], texts: &[(u64, &[u8])]) -> Program {
    let mut bytes = vec![0xccu8; 0x1000];
    bytes.resize(0x2000, 0);
    let mut put = |va: u64, b: &[u8]| {
        let off = saturating_usize(va - 0x1000);
        bytes[off..off + b.len()].copy_from_slice(b);
    };
    let mut main = Vec::new();
    for (k, &(entry, guard, expr, sig_at, sig)) in (0u64..).zip(methods) {
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
    for &(at, text) in texts {
        put(at, text);
    }
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

/// Builds the image of [`METHODS`] and their expressions.
fn widget() -> Program {
    let far = [&*b"1 == 1 && ".repeat(16), b"this->m_far\0"].concat();
    image(
        &METHODS,
        &[
            (NAME, b"this->m_name\0"),
            (SIZE, b"this->m_size > 0\0"),
            (FLAGS, b"this->m_flags < this->m_limit\0"),
            (COUNT, b"count > 0\0"),
            (ID, b"this->m_id\0"),
            (KEY, b"this->m_key\0"),
            (READY, b"this->IsReady()\0"),
            (DEPTH, b"this->m_depth\0"),
            (RECT, b"this->m_rect.w > 0\0"),
            (QUOTE, b"this->m_key == \"\" || this->m_val\0"),
            (FAR, &far),
        ],
    )
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

/// Each member the asserts spell is paired with the one offset the code
/// around its asserts reads, by how many sites agree, and a pairing the
/// sites dispute is listed and left open.
///
/// `m_name` is guarded at 0x270 by two methods: strong, and the answer
/// names the `set_type` call that states it. `m_size` is guarded at 0x10
/// by one method and at 0x18 by another: contested, both offsets listed
/// with their sites, neither stated. `m_flags < m_limit` names two
/// members over one guarded field, which says nothing of which is where:
/// both are weak, with no offset. `m_id` is guarded at 0x40 by two
/// methods and `m_key` at 0x40 by a third: both contested, each naming
/// the other. `this->IsReady()` is a getter, paired with nothing.
/// `m_depth`'s guards read a field of what +0x48 points at: never
/// strong. `m_rect.w` reaches into a member, so the field at +0x48 its
/// guards read may be a part of it: not paired. Two methods assert
/// `m_key == "" || m_val` over +0x58: two members, no pairing. `m_far` is
/// spelled past the 160 characters a pairing reads: listed, not paired.
/// The decompiler names none of +0x48 and +0x58 either. The listing of
/// names above is as it was.
#[test]
fn asserted_members_pair_with_the_offsets_their_guards_read() {
    let p = widget();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let all = asserted_fields_tsv(&p, &a, &o, "");
    for row in [
        "2\tm_name\tWidget",
        "2\tm_size\tWidget",
        "strong\tWidget\tm_name\t0x270\t0x1100, 0x1140",
        "contested\tWidget\tm_size\t0x10\t0x1180",
        "contested\tWidget\tm_size\t0x18\t0x11c0",
        "weak\tWidget\tm_flags\t-\t0x1200",
        "weak\tWidget\tm_limit\t-\t0x1200",
        "# state Widget's strong pairs: set_type(name=\"Widget\", fields=[\"0x270:m_name\"])",
    ] {
        assert!(all.lines().any(|l| l == row), "{row}:\n{all}");
    }
    assert!(
        !all.contains("strong\tWidget\tm_size") && !all.contains(":m_size\""),
        "a contested pairing was resolved:\n{all}"
    );
    for row in [
        "contested\tWidget\tm_id\t0x40\t0x1280, 0x12c0; 0x40 also asserted as m_key",
        "contested\tWidget\tm_key\t0x40\t0x1300; 0x40 also asserted as m_id",
    ] {
        assert!(all.lines().any(|l| l == row), "{row}:\n{all}");
    }
    assert!(
        !all.contains("\tWidget\tIsReady\t"),
        "a getter was paired as a member:\n{all}"
    );
    assert!(
        !all.lines()
            .any(|l| l.starts_with("strong\tWidget\tm_depth\t")),
        "a field behind a pointer was paired as the guarded field:\n{all}"
    );
    for row in [
        "2\tm_rect\tWidget",
        "1\tm_far\tWidget",
        "weak\tWidget\tm_val\t-\t0x14c0, 0x1500",
    ] {
        assert!(all.lines().any(|l| l == row), "{row}:\n{all}");
    }
    for paired in ["\tWidget\tm_rect\t", "\tm_key\t0x58", "\tWidget\tm_far\t"] {
        assert!(!all.contains(paired), "{paired}:\n{all}");
    }
    let names = field_names(&p, &a, &o, "Widget");
    assert_eq!(
        names.get(&0x270).map(String::as_str),
        Some("m_name"),
        "{names:?}"
    );
    assert!(
        !names.contains_key(&0x48) && !names.contains_key(&0x58),
        "{names:?}"
    );
    assert_eq!(
        all,
        asserted_fields_tsv(&p, &Analysis::compute(&p), &o, ""),
        "two analyses pair differently"
    );
    let size = asserted_fields_tsv(&p, &a, &o, "m_size");
    assert!(
        size.lines()
            .any(|l| l == "contested\tWidget\tm_size\t0x10\t0x1180"),
        "{size}"
    );
    assert!(
        !size.contains("m_name") && !size.contains("set_type("),
        "the filter let another member through:\n{size}"
    );
}

/// A member asserted at two offsets names neither of the class's fields,
/// while a member asserted at one offset keeps its name.
///
/// `m_size` is guarded at 0x10 by one method and at 0x18 by another: it
/// is at one of them at most, and `borer://asserts` lists the pair as
/// contested. Counted per offset, each vote won its offset, and every
/// reader of the class's field names took `m_size` at both (C-207).
#[test]
fn a_member_asserted_at_two_offsets_names_neither() {
    let p = widget();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let names = field_names(&p, &a, &o, "Widget");
    assert!(
        !names.contains_key(&0x10) && !names.contains_key(&0x18),
        "{names:?}"
    );
    assert_eq!(names.get(&0x270).map(String::as_str), Some("m_name"));
}

/// A long `__PRETTY_FUNCTION__` shows whole in the text, and a read of it
/// says where the rest starts.
///
/// The text holds it as a plain literal, return type, parameters and
/// template bindings; a read caps at 200 characters, so the string reads
/// whole in two reads.
///
/// GitHub issue 24's agent pruned the prefix fragments a cut left
/// instead of reading the type names behind them.
#[test]
fn a_long_pretty_function_reads_whole_in_parts() {
    let p = widget();
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1240).expect("decompiles");
    assert!(
        text.contains(&format!("\"{PRETTY}\"")),
        "the text cuts the long literal: {text}"
    );
    let first = read_values(&p, LONG, Kind::CStr, 1).expect("reads");
    assert_eq!(
        first[0].text,
        format!("\"{}...\" (len {})", &PRETTY[..200], PRETTY.len())
    );
    let rest = rest_of_cut(&first[0], Kind::CStr).expect("the read is cut");
    assert_eq!(rest, LONG + 200);
    let next = read_values(&p, rest, Kind::CStr, 1).expect("reads on");
    assert_eq!(
        next[0].text,
        format!("\"{}\" (len {})", &PRETTY[200..], PRETTY.len() - 200)
    );
    assert_eq!(rest_of_cut(&next[0], Kind::CStr), None);
    let short = read_values(&p, PATH, Kind::CStr, 1).expect("reads");
    assert_eq!(rest_of_cut(&short[0], Kind::CStr), None);
    assert_eq!(rest_of_cut(&short[0], Kind::U8), None);
}

/// `"this->m_count"`, asserted by the template methods.
const CNT: u64 = 0x2120;

/// The GCC, Clang and MSVC signatures of template methods, each with its
/// method's entry and where it sits, guarding `m_count` at +0x10.
const TEMPLATES: [(u64, u64, &str); 5] = [
    (0x1100, 0x2200, "void Box<T>::Grow() [with T = int]"),
    (0x1140, 0x2280, "void Box<T>::Grow() [with T = float]"),
    (0x1180, 0x2300, "void Box<int>::Fill(const T &) [T = int]"),
    (
        0x11c0,
        0x2380,
        "std::vector<T, A> Pool<T, A>::Take(unsigned long) [with T = std::pair<int, int>; A = std::allocator<std::pair<int, int> >]",
    ),
    (0x1200, 0x2480, "void __cdecl Box<int>::Drain(void)"),
];

/// A GCC or Clang template signature names and types nothing, and its
/// assert shows it whole, bindings included, as a plain literal; MSVC's,
/// which spells its arguments inline, names its method as before.
///
/// Every instantiation of `Box<T>::Grow` shares the name, `Fill`'s
/// parameter is the template's `T`, and spelling the bindings into a
/// signature multiplied its text: names drawn from the bindings were
/// false or unbounded (C-208). They are shown, not believed: no method
/// is named or typed, nor `Pool<T, A>` given a field.
#[test]
fn template_signatures_show_whole_and_name_nothing() {
    let methods = TEMPLATES.map(|(entry, at, sig)| (entry, Guard::Field(0x10), CNT, at, sig));
    let p = image(&methods, &[(CNT, b"this->m_count\0")]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for &(entry, _, sig) in &TEMPLATES[..4] {
        let f = a.function(entry).expect("found");
        assert!(f.name.is_none() && f.signature.is_none(), "{sig}");
        let text = decompile(&p, &a, &o, entry).expect("decompiles");
        assert!(text.contains(&format!("\"{sig}\"")), "{sig}: {text}");
    }
    let drain = a.function(0x1200).and_then(|f| f.name.clone());
    assert_eq!(drain.as_deref(), Some("Box<int>::Drain"));
    assert!(field_names(&p, &a, &o, "Pool<T, A>").is_empty());
}

/// A template method named and declared by hand, its `this` read, casts
/// no vote for its class's fields from its assert, as before template
/// signatures were shown whole.
///
/// The signature is a plain literal, no `__FUNCSIG__`, so the assert is
/// not read as one naming a member of `Box<int>`.
#[test]
fn a_named_template_method_casts_no_assert_vote() {
    let sig = TEMPLATES[0].2;
    let p = image(
        &[(0x1100, Guard::Field(0x10), CNT, 0x2200, sig)],
        &[(CNT, b"this->m_count\0")],
    );
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1100, "Box<int>::Grow".to_owned());
    let proto = Proto::parse("void Grow(void *this)").expect("parses");
    o.prototypes.insert(0x1100, proto);
    assert!(field_names(&p, &a, &o, "Box<int>").is_empty());
}

/// `"bits/stl_vector.h"`, the file a libstdc++ assert cites.
const STL: u64 = 0x2140;

/// A libstdc++ assert, which cites its file before its condition, is not
/// folded into `assert(bits/stl_vector.h);` in the skeleton, and its
/// condition shows.
///
/// `std::__glibcxx_assert_fail` takes the file, the line, the function and
/// the condition; here the reporter's path slot holds the condition, so
/// the file comes first and the template signature last. Shown as
/// `__FUNCSIG__(...)`, the signature made the call read as a guarded
/// assert whose first literal is its condition.
#[test]
fn a_libstdcxx_assert_is_not_folded_on_its_file() {
    let sig = "std::vector<_Tp, _Alloc>::reference std::vector<_Tp, _Alloc>::operator[](size_type) [with _Tp = int; _Alloc = std::allocator<int>; reference = int&; size_type = long unsigned int]";
    let p = image(
        &[(0x1100, Guard::Field(0x10), STL, 0x2200, sig)],
        &[
            (STL, b"bits/stl_vector.h\0"),
            (PATH, b"__n < this->size()\0"),
        ],
    );
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1100).expect("decompiles");
    let outline = skeleton(&text);
    assert!(!outline.contains("assert("), "{outline}");
    assert!(outline.contains("\"__n < this->size()\""), "{outline}");
}
