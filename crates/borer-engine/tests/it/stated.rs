//! Fields an agent states of a class borer recovered: the name it gives
//! one offset prints wherever the class's fields do, and nothing else of
//! the class, or of another class, changes.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::classes::{class_layout, render_layout};
use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::stated::Field;
use borer_engine::analysis::utypes::parse_type;
use borer_engine::analysis::{Analysis, EnumSource, Overlay};
use borer_engine::program::{Arch, Program, Section};

/// The class the tests state fields of: its table is at 0x2800.
const CLASS: &str = "class_2800";

/// The methods of [`CLASS`] that read and write its field at 0x270.
const METHODS: [u64; 2] = [0x1040, 0x1080];

/// A method of the other class, which has a field at 0x270 too.
const OTHER_METHOD: u64 = 0x1140;

/// A raw x86-64 image of two classes nothing names, each a constructor
/// storing its table and two virtual methods.
///
/// `class_2800` (table at 0x2800) has a constructor at 0x1000 and the
/// methods 0x1040 and 0x1080; between them they access the fields 0x10,
/// 0x14 and 0x270 as dwords, 0x18 as a qword and as a dword, and 0x20 as
/// a byte. `class_2900` (table at 0x2900) has a constructor at 0x1100 and the
/// methods 0x1140 and 0x1180, over dwords at 0x30, 0x34 and 0x270. A
/// pointer after each table seeds its constructor.
fn two_classes() -> Program {
    let mut bytes = vec![0xccu8; 0x2000];
    let mut put = |va: usize, piece: &[u8]| {
        bytes[va - 0x1000..va - 0x1000 + piece.len()].copy_from_slice(piece);
    };
    put(
        0x1000,
        &[
            0x48, 0x8d, 0x05, 0xf9, 0x17, 0x00, 0x00, // ASM: lea rax, [rip+0x17f9]
            0x48, 0x89, 0x01, // ASM: mov [rcx], rax
            0xc7, 0x81, 0x70, 0x02, 0x00, 0x00, // ASM: mov dword [rcx+0x270],
            0xff, 0xff, 0xff, 0xff, // ASM:   0xffffffff
            0x48, 0xc7, 0x41, 0x18, 0x00, 0x00, 0x00, 0x00, // ASM: mov qword [rcx+0x18], 0
            0xc6, 0x41, 0x20, 0x00, // ASM: mov byte [rcx+0x20], 0
            0xc3, // ASM: ret
        ],
    );
    put(
        0x1040,
        &[
            0x8b, 0x81, 0x70, 0x02, 0x00, 0x00, // ASM: mov eax, [rcx+0x270]
            0x03, 0x41, 0x10, // ASM: add eax, [rcx+0x10]
            0x03, 0x41, 0x18, // ASM: add eax, [rcx+0x18]
            0x89, 0x41, 0x14, // ASM: mov [rcx+0x14], eax
            0xc3, // ASM: ret
        ],
    );
    put(
        0x1080,
        &[
            0x89, 0x91, 0x70, 0x02, 0x00, 0x00, // ASM: mov [rcx+0x270], edx
            0x48, 0x8b, 0x41, 0x18, // ASM: mov rax, [rcx+0x18]
            0xc6, 0x41, 0x20, 0x01, // ASM: mov byte [rcx+0x20], 1
            0xc3, // ASM: ret
        ],
    );
    put(
        0x1100,
        &[
            0x48, 0x8d, 0x05, 0xf9, 0x17, 0x00, 0x00, // ASM: lea rax, [rip+0x17f9]
            0x48, 0x89, 0x01, // ASM: mov [rcx], rax
            0xc3, // ASM: ret
        ],
    );
    put(
        0x1140,
        &[
            0x8b, 0x81, 0x70, 0x02, 0x00, 0x00, // ASM: mov eax, [rcx+0x270]
            0x03, 0x41, 0x30, // ASM: add eax, [rcx+0x30]
            0x89, 0x41, 0x34, // ASM: mov [rcx+0x34], eax
            0xc3, // ASM: ret
        ],
    );
    put(
        0x1180,
        &[
            0x8b, 0x41, 0x30, // ASM: mov eax, [rcx+0x30]
            0xc3, // ASM: ret
        ],
    );
    for (table, slots) in [
        (0x2800, [0x1040u64, 0x1080, 0, 0x1000]),
        (0x2900, [0x1140, 0x1180, 0, 0x1100]),
    ] {
        for (k, slot) in slots.iter().enumerate() {
            put(table + 8 * k, &slot.to_le_bytes());
        }
    }
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    )
}

/// An overlay stating fields of [`CLASS`], inserted in the order given.
///
/// # Arguments
///
/// * `fields` - `(offset, name, type)` per field, the type as the tools
///   spell it or `None` for a name alone.
fn stating(fields: &[(u64, &str, Option<&str>)]) -> Overlay {
    let mut o = Overlay::default();
    for &(off, name, ty) in fields {
        let field = Field {
            name: name.to_owned(),
            ty: ty.map(|t| parse_type(t).expect("a type the language spells")),
        };
        o.fields
            .entry(CLASS.to_owned())
            .or_default()
            .insert(off, field);
    }
    o
}

/// The rows of a class's layout, one per field.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
/// * `o` - The overlay.
/// * `class` - The class.
fn rows(p: &Program, a: &Analysis, o: &Overlay, class: &str) -> Vec<String> {
    let layout = class_layout(p, a, o, class).expect("the class has methods");
    render_layout(&layout, a, o)
        .lines()
        .filter(|l| l.starts_with('+'))
        .map(str::to_owned)
        .collect()
}

/// One field named on a class of six leaves the five others byte for
/// byte, and its own row carries the name and says it is stated.
#[test]
fn one_stated_field_leaves_every_other_row_of_the_layout_as_it_was() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let before = rows(&p, &a, &Overlay::default(), CLASS);
    assert_eq!(before.len(), 6, "{before:#?}");
    let named = stating(&[(0x270, "m_currentPipeline", None)]);
    let after = rows(&p, &a, &named, CLASS);
    let differing: Vec<(&String, &String)> = before
        .iter()
        .zip(&after)
        .filter(|(was, now)| was != now)
        .collect();
    assert_eq!(
        differing,
        [(
            &"+0x270  u32        1/2   ctor_or_dtor, vfunc_0, vfunc_1  [= 0xffffffff]".to_owned(),
            &"+0x270  u32 m_currentPipeline  1/2   ctor_or_dtor, vfunc_0, vfunc_1  [stated; = 0xffffffff]"
                .to_owned()
        )]
    );
    let typed = stating(&[(0x270, "m_currentPipeline", Some("u32"))]);
    assert!(
        rows(&p, &a, &typed, CLASS)[5].ends_with("[stated u32; = 0xffffffff]"),
        "a stated type is named beside the mark"
    );
    assert_eq!(
        rows(&p, &a, &named, "class_2900"),
        rows(&p, &a, &Overlay::default(), "class_2900"),
        "the other class has a field at 0x270 too, and nothing is stated of it"
    );
}

/// Every method of the class prints the stated name, with no typing of
/// `this`, and a method of another class reading its own field at the same
/// offset prints what it printed.
#[test]
fn a_stated_field_prints_in_the_class_s_methods_and_no_other_class_s() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let named = stating(&[(0x270, "m_currentPipeline", None)]);
    let text = |o: &Overlay, entry: u64| decompile_named(&p, &a, o, entry).expect("decompiles");
    for entry in METHODS {
        assert!(
            text(&plain, entry).contains("this->field_0x270"),
            "{}",
            text(&plain, entry)
        );
        let stated = text(&named, entry);
        assert!(stated.contains("this->m_currentPipeline"), "{stated}");
        assert!(!stated.contains("field_0x270"), "{stated}");
    }
    assert_eq!(text(&named, OTHER_METHOD), text(&plain, OTHER_METHOD));
    assert!(text(&named, OTHER_METHOD).contains("this->field_0x270"));
}

/// The same fields stated in another order are the same overlay: one
/// fingerprint, and the same bytes from a fresh analysis of each.
#[test]
fn stated_fields_read_the_same_in_any_order() {
    let p = two_classes();
    let fields = [
        (0x270, "m_currentPipeline", Some("u32")),
        (0x18, "m_next", None),
        (0x20, "m_bound", Some("u8")),
    ];
    let mut reversed = fields;
    reversed.reverse();
    let (one, other) = (stating(&fields), stating(&reversed));
    assert_eq!(one.fingerprint(), other.fingerprint());
    assert_ne!(one.fingerprint(), Overlay::default().fingerprint());
    assert_ne!(
        stating(&fields[..1]).fingerprint(),
        stating(&[(0x270, "m_currentPipeline", None)]).fingerprint(),
        "a field's type is part of what is stated"
    );
    let texts = |o: &Overlay| {
        let a = Analysis::compute(&p);
        let methods: Vec<String> = METHODS
            .iter()
            .map(|&entry| decompile_named(&p, &a, o, entry).expect("decompiles"))
            .collect();
        (methods, rows(&p, &a, o, CLASS))
    };
    assert_eq!(texts(&one), texts(&other));
    assert!(
        texts(&one).0[1].contains("this->m_next"),
        "{:#?}",
        texts(&one)
    );
}

/// A field stated of one class lets go of the texts of that class's
/// methods alone: a method of another class is answered from what was
/// built before the statement.
///
/// The overlays read the binary's own name tables, as the tools' do: what
/// is read under the empty overlay stays filed there, in force for every
/// session.
#[test]
fn stating_a_field_rebuilds_only_the_class_s_own_texts() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let tools = |o: Overlay| Overlay {
        enum_source: EnumSource::Binary,
        ..o
    };
    let plain = tools(Overlay::default());
    let before = decompile_named(&p, &a, &plain, METHODS[0]).expect("decompiles");
    let other = decompile_named(&p, &a, &plain, OTHER_METHOD).expect("decompiles");
    let named = tools(stating(&[(0x270, "m_currentPipeline", None)]));
    a.derived.moved(&a, &plain, &named);
    let built = a.derived.builds();
    assert_eq!(decompile_named(&p, &a, &named, OTHER_METHOD), Some(other));
    assert_eq!(
        a.derived.builds(),
        built,
        "the other class's text was built again"
    );
    let after = decompile_named(&p, &a, &named, METHODS[0]).expect("decompiles");
    assert_ne!(after, before);
    assert!(
        a.derived.builds() > built,
        "the class's own text is rebuilt"
    );
}
