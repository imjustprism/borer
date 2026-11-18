//! What a build that keeps its assertions says.
//!
//! It covers the next steps a function that asserts points at, and each member
//! its asserts spell paired with the field offset the code around them reads,
//! a long `__PRETTY_FUNCTION__` read whole in parts, and template
//! signatures shown whole without naming anything.
//!
//! Each image is a stripped build with assertions on: every method guards
//! one field and reports a failure as `assert("<expression>", "<file>",
//! <line>, "<__PRETTY_FUNCTION__>")`, the signature literal naming the
//! method, and nothing else names it. The `Widget` image spells its
//! members `this->m_name`; the `Registry` image spells them bare
//! (`!m_stop`, `m_replicas.size()`), the shape GitHub issue 24's GCC
//! build has.

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
/// template, 292 characters: its arguments come last, after the 200
/// characters a read shows.
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

/// The `Widget` answer, every member spelled after `this->`, as it was
/// before bare names were read.
const WIDGET_ANSWER: [&str; 25] = [
    "# 11 of 11 asserted field names\n",
    "# functions\tfield\tclasses\n",
    "3\tm_key\tWidget\n",
    "2\tIsReady\tWidget\n",
    "2\tm_depth\tWidget\n",
    "2\tm_id\tWidget\n",
    "2\tm_name\tWidget\n",
    "2\tm_rect\tWidget\n",
    "2\tm_size\tWidget\n",
    "2\tm_val\tWidget\n",
    "1\tm_far\tWidget\n",
    "1\tm_flags\tWidget\n",
    "1\tm_limit\tWidget\n",
    "# 9 pairings of asserted members with field offsets, from the code around each assert: 1 strong (two or more functions' single-offset sites agree), 4 contested (sites disagree; not resolved), 4 weak (fewer than two functions, or not verified against the rest; offset - when no site reads one field)\n",
    "# tier\tclass\tmember\toffset\tsites (function entries, xN for N sites)\n",
    "strong\tWidget\tm_name\t0x270\t0x1100, 0x1140\n",
    "contested\tWidget\tm_id\t0x40\t0x1280, 0x12c0; 0x40 also asserted as m_key\n",
    "contested\tWidget\tm_key\t0x40\t0x1300; 0x40 also asserted as m_id\n",
    "contested\tWidget\tm_size\t0x10\t0x1180\n",
    "contested\tWidget\tm_size\t0x18\t0x11c0\n",
    "weak\tWidget\tm_depth\t-\t0x13c0, 0x1400\n",
    "weak\tWidget\tm_flags\t-\t0x1200\n",
    "weak\tWidget\tm_limit\t-\t0x1200\n",
    "weak\tWidget\tm_val\t-\t0x14c0, 0x1500\n",
    "# state Widget's strong pairs: set_type(name=\"Widget\", fields=[\"0x270:m_name\"])\n",
];

/// Reading bare names leaves an answer of `this->` spellings as it was,
/// byte for byte.
///
/// `count > 0`, asserted under a template signature that names no
/// method, once listed `1 count` as a name, and both headers carried a
/// note on bare names no row needed.
#[test]
fn a_this_answer_is_as_it_was() {
    let p = widget();
    let a = Analysis::compute(&p);
    let all = asserted_fields_tsv(&p, &a, &Overlay::default(), "");
    assert_eq!(all, WIDGET_ANSWER.concat());
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

/// `"!m_stop"`, a member spelled bare.
const STOP: u64 = 0x2120;

/// `"m_replicas.size()"`, a bare member reached into.
const REPLICAS: u64 = 0x2140;

/// `"index >= 0 && index < (int)m_replicas.size()"`: a parameter and a
/// member, both spelled bare.
const INDEX: u64 = 0x2160;

/// `"m_entityComponents.size() == m_entityBitsets.size()"`, two bare
/// members.
const BOTH: u64 = 0x21a0;

/// `"value < limit"`, asserted by a free function.
const CLAMP: u64 = 0x21e0;

/// Methods whose asserts spell members bare, as GitHub issue 24's GCC
/// build does.
///
/// `Stop` and `Halt` guard `m_stop` at +0x20, `At` and `Get`
/// guard +0x28 under a condition naming `index` and `m_replicas`. Last,
/// `tools::Clamp` is a free function in a namespace, its one argument
/// the one register it reads.
const BARE: [(u64, Guard, u64, u64, &str); 7] = [
    (
        0x1100,
        Guard::Field(0x20),
        STOP,
        0x2200,
        "void Registry::Stop()",
    ),
    (
        0x1140,
        Guard::Field(0x20),
        STOP,
        0x2240,
        "void Registry::Halt()",
    ),
    (
        0x1180,
        Guard::Field(0x28),
        REPLICAS,
        0x2280,
        "void Registry::Count()",
    ),
    (
        0x11c0,
        Guard::Field(0x28),
        INDEX,
        0x22c0,
        "void Registry::At()",
    ),
    (
        0x1200,
        Guard::Field(0x28),
        INDEX,
        0x2300,
        "void Registry::Get()",
    ),
    (
        0x1240,
        Guard::Field(0x38),
        BOTH,
        0x2340,
        "void Registry::Check()",
    ),
    (
        0x1280,
        Guard::Field(0x8),
        CLAMP,
        0x2380,
        "void tools::Clamp(int)",
    ),
];

/// Builds the image of [`BARE`] and their expressions.
fn registry() -> Program {
    image(
        &BARE,
        &[
            (STOP, b"!m_stop\0"),
            (REPLICAS, b"m_replicas.size()\0"),
            (INDEX, b"index >= 0 && index < (int)m_replicas.size()\0"),
            (
                BOTH,
                b"m_entityComponents.size() == m_entityBitsets.size()\0",
            ),
            (CLAMP, b"value < limit\0"),
        ],
    )
}

/// The header line of the tier bare pairs are listed in.
const BARE_HEADER: &str =
    "a bare name may be a local or a parameter that holds the field, so none is strong or stated";

/// Members an assert spells bare are paired in a tier of their own, never
/// strong, never stated, and never listed as names.
///
/// `!m_stop` over +0x20 in two methods is `bare`, with both sites.
/// `m_replicas.size()` reaches into its member, so +0x28 may be a part of
/// it: not paired. `index >= 0 && index < (int)m_replicas.size()` names
/// two candidates over one field, which says nothing of which is where,
/// and `index` is a parameter: paired with nothing, and not offered with
/// no offset either, since nothing shows a bare name is a member. The
/// decompiler names fields from `this->` alone.
#[test]
fn bare_members_are_paired_in_their_own_tier() {
    let p = registry();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let all = asserted_fields_tsv(&p, &a, &o, "");
    let header = all.lines().find(|l| l.contains(BARE_HEADER));
    assert!(
        header.is_some_and(|l| l.starts_with("# 1 bare pairings")),
        "{all}"
    );
    assert!(
        all.lines()
            .any(|l| l == "bare\tRegistry\tm_stop\t0x20\t0x1100, 0x1140"),
        "{all}"
    );
    assert!(
        !all.contains("strong\t") && !all.contains("set_type("),
        "a bare pairing was made strong:
{all}"
    );
    for member in [
        "index",
        "m_replicas",
        "m_entityComponents",
        "m_entityBitsets",
    ] {
        assert!(
            !all.contains(member),
            "{member} was listed:
{all}"
        );
    }
    assert!(field_names(&p, &a, &o, "Registry").is_empty());
}

/// `"!stopped"`, a local that holds the field its guard reads.
const STOPPED: u64 = 0x2120;

/// `"index >= 0"`, a parameter of the method it was inlined from.
const INDEX0: u64 = 0x2140;

/// Methods whose one bare candidate is no member.
///
/// `Stop` and `Halt` hold `bool stopped = m_stop; assert(!stopped);`, the
/// local the guard of +0x20 reads. `Run` and `Step`, as the overlay names
/// them, inlined `Registry::CheckIndex(int index) const`, which asserts
/// `index >= 0`, and its twin `CheckSlot` as `CheckIndex(m_cursor)`, the
/// guard reading +0x30.
const LOCALS: [(u64, Guard, u64, u64, &str); 4] = [
    (
        0x1100,
        Guard::Field(0x20),
        STOPPED,
        0x2200,
        "void Registry::Stop()",
    ),
    (
        0x1140,
        Guard::Field(0x20),
        STOPPED,
        0x2240,
        "void Registry::Halt()",
    ),
    (
        0x1180,
        Guard::Field(0x30),
        INDEX0,
        0x2280,
        "void Registry::CheckIndex(int) const",
    ),
    (
        0x11c0,
        Guard::Field(0x30),
        INDEX0,
        0x22c0,
        "void Registry::CheckSlot(int) const",
    ),
];

/// A bare name that is a local or a parameter holding the field pairs
/// strong nowhere and is stated nowhere: the bytes cannot tell it from a
/// member.
///
/// Two methods agreeing on `stopped` at +0x20 is `bare`, never strong. An
/// assert inlined from another method of the class casts no bare vote,
/// so the overlay's `Run` and `Step` pair `index` with nothing.
#[test]
fn a_bare_local_or_parameter_pairs_strong_nowhere() {
    let p = image(
        &LOCALS,
        &[(STOPPED, b"!stopped\0"), (INDEX0, b"index >= 0\0")],
    );
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1180, "Registry::Run".to_owned());
    o.names.insert(0x11c0, "Registry::Step".to_owned());
    let all = asserted_fields_tsv(&p, &a, &o, "");
    assert!(
        !all.contains("strong\t") && !all.contains("set_type("),
        "a local or a parameter was paired strong:
{all}"
    );
    assert!(
        all.lines()
            .any(|l| l == "bare\tRegistry\tstopped\t0x20\t0x1100, 0x1140"),
        "{all}"
    );
    assert!(!all.contains("index\t0x30"), "{all}");
    assert!(field_names(&p, &a, &o, "Registry").is_empty());
}

/// `L"this->m_x"`, as MSVC writes a wide condition.
const WIDE: u64 = 0x2120;

/// Methods asserting a wide condition over +0x20.
const WIDE_ASSERTS: [(u64, Guard, u64, u64, &str); 2] = [
    (0x1100, Guard::Field(0x20), WIDE, 0x2200, "void Wide::Get()"),
    (0x1140, Guard::Field(0x20), WIDE, 0x2240, "void Wide::Put()"),
];

/// A one-character read of a wide literal names nothing.
///
/// Read as bytes, `L"this->m_x"` stops after its first character, `t`,
/// which once read as a bare candidate of `Wide`.
#[test]
fn a_wide_literal_read_as_bytes_names_nothing() {
    let wide: Vec<u8> = "this->m_x\0"
        .encode_utf16()
        .flat_map(u16::to_le_bytes)
        .collect();
    let p = image(&WIDE_ASSERTS, &[(WIDE, &wide)]);
    let a = Analysis::compute(&p);
    let all = asserted_fields_tsv(&p, &a, &Overlay::default(), "");
    assert!(
        !all.contains("\tt\t") && !all.contains(BARE_HEADER),
        "{all}"
    );
}

/// A function's assert conditions are read once per analysis: every
/// read, filter and page of the index asks the memo.
#[test]
fn assert_conditions_are_read_once_per_function() {
    let p = registry();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let all = asserted_fields_tsv(&p, &a, &o, "");
    assert_eq!(
        a.derived.held("assert_conditions"),
        BARE.len(),
        "{:?}",
        a.derived
    );
    assert_eq!(asserted_fields_tsv(&p, &a, &o, ""), all);
    asserted_fields_tsv(&p, &a, &o, "m_stop");
    assert_eq!(a.derived.held("assert_conditions"), BARE.len());
}

/// A method whose only assert spells its member bare points at its
/// class's bare names, saying they may be no members.
///
/// A free function's bare assert does not read its namespace as a class.
#[test]
fn a_bare_assert_points_at_the_asserts() {
    let p = registry();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let step = "borer://asserts/Registry (the names its class's asserts spell bare: members, locals or parameters), borer://sources/widget.cpp (the source file they cite)";
    for entry in [0x1100, 0x11c0] {
        let header = answer_header(&p, &a, &o, entry, None).unwrap_or_default();
        assert!(header.contains(&format!("// next: {step}")), "{header}");
    }
    let free = next_steps(&p, &a, &o, 0x1280);
    assert!(
        free.iter().all(|s| !s.contains("borer://asserts")),
        "{free:?}"
    );
}

/// `"this->m_owner"`, asserted by a method of another class.
const OWNER: u64 = 0x2120;

/// `"this->m_flag"`, asserted by a method of the caller's own class.
const FLAG: u64 = 0x2140;

/// Methods of `A`, renamed so by the overlay, whose asserts were inlined:
/// `Fetch` and `Load` from `B::Get` and `B::Peek`, guarding +0x40, and
/// `Own` from `A::Check`, guarding +0x48.
const INLINED: [(u64, Guard, u64, u64, &str); 3] = [
    (0x1100, Guard::Field(0x40), OWNER, 0x2200, "void B::Get()"),
    (0x1140, Guard::Field(0x40), OWNER, 0x2240, "void B::Peek()"),
    (0x1180, Guard::Field(0x48), FLAG, 0x2280, "void A::Check()"),
];

/// An assert inlined from another class's method names none of the
/// caller's fields, while one inlined from its own class's names them.
///
/// GitHub issue 24's `vulkan.hpp` asserts `m_owner` and `m_dispatch` in
/// every caller they were inlined into, and each caller's guard read its
/// own object, so the pairing put `VulkanRenderContext::m_owner` at four
/// offsets.
#[test]
fn an_inlined_assert_names_only_its_own_class() {
    let p = image(
        &INLINED,
        &[(OWNER, b"this->m_owner\0"), (FLAG, b"this->m_flag\0")],
    );
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    for (entry, name) in [
        (0x1100, "A::Fetch"),
        (0x1140, "A::Load"),
        (0x1180, "A::Own"),
    ] {
        o.names.insert(entry, name.to_owned());
    }
    let text = decompile(&p, &a, &o, 0x1100).expect("decompiles");
    assert!(text.contains("__FUNCSIG__(B::Get)"), "{text}");
    let names = field_names(&p, &a, &o, "A");
    assert!(!names.contains_key(&0x40), "{names:?}");
    assert_eq!(names.get(&0x48).map(String::as_str), Some("m_flag"));
    let all = asserted_fields_tsv(&p, &a, &o, "");
    assert!(!all.contains("\tA\tm_owner\t0x40"), "{all}");
    assert!(
        all.lines().any(|l| l == "weak\tA\tm_flag\t0x48\t0x1180"),
        "{all}"
    );
}
