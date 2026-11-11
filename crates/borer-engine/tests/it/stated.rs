//! Fields an agent states of a class borer recovered: the name it gives
//! one offset prints wherever the class's fields do, and nothing else of
//! the class, or of another class, changes.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::apply::from_pointer;
use borer_engine::analysis::classes::{class_layout, render_layout};
use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::stated::{
    Field, Mode, Statement, object_class, plan, plan_at, plan_class, undefined,
};
use borer_engine::analysis::utypes::{UserType, build_enum, list_tsv, parse_type};
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
/// a byte. `class_2900` (table at 0x2900) has a constructor at 0x1100 and
/// the methods 0x1140 and 0x1180, over dwords at 0x30, 0x34 and 0x270, the
/// one at 0x30 read by eight instructions. A pointer after each table
/// seeds its constructor.
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
    put(0x1180, &[0x8b, 0x41, 0x30]); // ASM: mov eax, [rcx+0x30]
    for k in 0..6 {
        put(0x1183 + 3 * k, &[0x03, 0x41, 0x30]); // ASM: add eax, [rcx+0x30]
    }
    put(0x1195, &[0xc3]); // ASM: ret
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

/// One stated field, as a test spells it.
///
/// # Arguments
///
/// * `name` - The field's name.
/// * `ty` - Its type as the tools spell it, or `None` for the name alone.
fn field(name: &str, ty: Option<&str>) -> Field {
    Field {
        name: name.to_owned(),
        ty: ty.map(|t| parse_type(t).expect("a type the language spells")),
    }
}

/// An overlay stating fields of [`CLASS`], inserted in the order given.
///
/// # Arguments
///
/// * `fields` - `(offset, name, type)` per field, as [`field`] takes them.
fn stating(fields: &[(u64, &str, Option<&str>)]) -> Overlay {
    let mut o = Overlay::default();
    for &(off, name, ty) in fields {
        o.fields
            .entry(CLASS.to_owned())
            .or_default()
            .insert(off, field(name, ty));
    }
    o
}

/// Plans a statement over an overlay and applies it.
///
/// # Arguments
///
/// * `image` - The image and its analysis.
/// * `o` - The overlay the statement is made over.
/// * `name` - The struct or class.
/// * `fields` - `(offset, name, type)` per field, as [`field`] takes them.
/// * `mode` - Whether the fields merge or replace.
///
/// # Returns
///
/// What the dry run says, and the overlay with the plan applied.
///
/// # Errors
///
/// The refusal, when the statement is refused.
fn state(
    (p, a): (&Program, &Analysis),
    o: &Overlay,
    name: &str,
    fields: &[(u64, &str, Option<&str>)],
    mode: Mode,
) -> Result<(String, Overlay), String> {
    let fields: Vec<(u64, Field)> = fields
        .iter()
        .map(|&(off, n, ty)| (off, field(n, ty)))
        .collect();
    let statement = Statement {
        name,
        size: None,
        fields: &fields,
        mode,
    };
    let plan = plan(p, a, o, &statement)?;
    let said = plan.would();
    let mut after = o.clone();
    plan.apply(&mut after);
    Ok((said, after))
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

/// One field named through a plan says what it keeps and what it changes,
/// leaves an overlay stating that field alone, and a later statement
/// keeps the earlier one.
#[test]
fn a_plan_names_one_field_and_keeps_every_other() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let name_only = [(0x270, "m_currentPipeline", None)];
    let (said, named) = state((&p, &a), &plain, CLASS, &name_only, Mode::Merge).expect("plans");
    assert_eq!(
        said,
        "state 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline (accessed 4 byte(s) wide)"
    );
    assert_eq!(named.fields, stating(&name_only).fields);
    assert_eq!(
        named.types, plain.types,
        "a class's fields define no struct"
    );
    let (again, same) = state((&p, &a), &named, CLASS, &name_only, Mode::Merge).expect("plans");
    assert_eq!(
        again,
        "state 1 field(s) of class class_2800: 6 kept, 0 changed, 0 new"
    );
    assert_eq!(same.fingerprint(), named.fingerprint());
    let more = [
        (0x300, "m_extra", Some("u32")),
        (0x10, "m_count", Some("u32")),
    ];
    let (said, both) = state((&p, &a), &named, CLASS, &more, Mode::Merge).expect("plans");
    assert_eq!(
        said,
        "state 2 field(s) of class class_2800: 5 kept, 1 changed, 1 new: +0x10 field_0x10 -> m_count u32, +0x300 m_extra u32 (new)"
    );
    assert_eq!(
        both.fields,
        stating(&[name_only[0], more[0], more[1]]).fields,
        "the field stated before stays"
    );
    let renamed = [(0x270, "m_pipeline", Some("u32"))];
    let (said, _) = state((&p, &a), &both, CLASS, &renamed, Mode::Merge).expect("plans");
    assert_eq!(
        said,
        "state 1 field(s) of class class_2800: 6 kept, 1 changed, 0 new: +0x270 m_currentPipeline -> m_pipeline u32"
    );
}

/// A stated type is held to the widths the class's code accesses the
/// field at, by its size alone.
///
/// A type as wide as an access is accepted whatever it is, a field
/// accessed at two widths takes either, an array or a struct is not held
/// to its first element's width, and a size the code never uses is refused
/// with both widths, the instructions and the statement that keeps the
/// width; a typedef and an enum are held by the size they stand for.
#[test]
fn a_stated_type_conflicts_only_by_a_size_the_code_never_uses() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let vec = [(0, "x", Some("f32")), (4, "y", Some("f32"))];
    let (_, o) = state((&p, &a), &Overlay::default(), "Vec", &vec, Mode::Merge).expect("defines");
    let typed = |off: u64, ty: &'static str| {
        state(
            (&p, &a),
            &o,
            CLASS,
            &[(off, "m_field", Some(ty))],
            Mode::Merge,
        )
    };
    for (off, ty) in [
        (0x270, "u32"),
        (0x270, "i32"),
        (0x270, "f32"),
        (0x18, "u64"),
        (0x18, "u32"),
        (0x18, "u8 *"),
        (0x18, "Vec *"),
        (0x10, "char[16]"),
        (0x10, "Vec"),
    ] {
        assert!(
            typed(off, ty).is_ok(),
            "{ty} at {off:#x}: {:?}",
            typed(off, ty)
        );
    }
    assert_eq!(
        typed(0x270, "u64").expect_err("eight bytes where the code reads four"),
        "field m_field at +0x270 of class class_2800 is stated u64, 8 byte(s) wide, but the class's code accesses it 4 byte(s) wide at 0x100a (class_2800::ctor_or_dtor), 0x1040 (class_2800::vfunc_0), 0x1080 (class_2800::vfunc_1); state a type of that width, or leave the type out (0x270:m_field) to keep the width the code uses"
    );
    let refused = typed(0x18, "u16").expect_err("two bytes where the code reads four and eight");
    assert!(
        refused.contains(
            "is stated u16, 2 byte(s) wide, but the class's code accesses it 4/8 byte(s) wide at 0x"
        ),
        "{refused}"
    );
    assert_eq!(
        typed(0x18, "Nope *").expect_err("a type nothing defines"),
        "field m_field's type Nope * resolves to no size at 0x18"
    );
    assert_eq!(
        typed(u64::MAX - 1, "u32").expect_err("a field that ends past every address"),
        "field m_field's type u32 resolves to no size at 0xfffffffffffffffe"
    );
    let mut named = o.clone();
    for (name, stands_for) in [
        ("Wide", "u64"),
        ("Wider", "Wide"),
        ("Label", "char[16]"),
        ("Pair", "Vec"),
    ] {
        let alias = UserType::Alias(parse_type(stands_for).expect("a type the language spells"));
        named.types.insert(name.to_owned(), alias);
    }
    let state_enum = build_enum("State", 8, &[(1, "Run".to_owned())]).expect("an enum");
    named.types.insert("State".to_owned(), state_enum);
    let aliased = |off: u64, ty: &'static str| {
        state(
            (&p, &a),
            &named,
            CLASS,
            &[(off, "m_field", Some(ty))],
            Mode::Merge,
        )
    };
    for ty in ["Wide", "Wider", "State"] {
        let refused =
            aliased(0x270, ty).expect_err("a name for eight bytes where the code reads four");
        assert!(
            refused.contains(&format!(
                "is stated {ty}, 8 byte(s) wide, but the class's code accesses it 4 byte(s) wide"
            )),
            "{refused}"
        );
        assert!(aliased(0x18, ty).is_ok(), "{ty} where the code reads eight");
    }
    for ty in ["Label", "Pair"] {
        assert!(aliased(0x10, ty).is_ok(), "{ty} names an array or a struct");
    }
    let many = [(0x30, "m_field", Some("u64"))];
    let refused = state((&p, &a), &o, "class_2900", &many, Mode::Merge)
        .expect_err("eight instructions read four bytes");
    assert!(
        refused.contains(" at 0x1146 (class_2900::vfunc_0), 0x1180 (class_2900::vfunc_1), ")
            && refused.contains(", 0x118c (class_2900::vfunc_1) and 2 more; state a type"),
        "{refused}"
    );
}

/// Replacing, asked for, leaves the class stating the new fields alone
/// and says which it dropped; the layout its methods show stays, and a
/// class left stating nothing leaves the overlay.
#[test]
fn a_replacing_statement_drops_what_the_class_stated_before() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let before = stating(&[
        (0x270, "m_currentPipeline", Some("u32")),
        (0x18, "m_next", None),
    ]);
    let stated = [
        (0x20, "m_bound", None),
        (0x270, "m_currentPipeline", Some("u32")),
    ];
    let (said, after) = state((&p, &a), &before, CLASS, &stated, Mode::Replace).expect("plans");
    assert_eq!(
        said,
        "state 2 field(s) of class class_2800: 4 kept, 1 changed, 0 new, 1 dropped: +0x20 field_0x20 -> m_bound (accessed 1 byte(s) wide), +0x18 m_next (dropped)"
    );
    assert_eq!(after.fields, stating(&stated).fields);
    assert_eq!(rows(&p, &a, &after, CLASS).len(), 6);
    let (_, merged) = state((&p, &a), &before, CLASS, &stated[..1], Mode::Merge).expect("plans");
    assert_eq!(
        merged.fields,
        stating(&[stated[0], stated[1], (0x18, "m_next", None)]).fields,
        "merged, the same statement drops nothing"
    );
    let (said, cleared) = state((&p, &a), &before, CLASS, &[], Mode::Replace).expect("plans");
    assert_eq!(
        said,
        "state 0 field(s) of class class_2800: 4 kept, 0 changed, 0 new, 2 dropped: +0x18 m_next (dropped), +0x270 m_currentPipeline u32 (dropped)"
    );
    assert!(
        cleared.fields.is_empty(),
        "a class left stating nothing is no entry of the overlay"
    );
    assert_eq!(cleared.fingerprint(), Overlay::default().fingerprint());
}

/// A user struct takes stated fields by offset too: a field restated
/// without a type keeps the one it had, the others stay, the size never
/// shrinks, and replacing leaves the stated fields alone.
#[test]
fn a_user_struct_merges_stated_fields_and_replaces_only_when_asked() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let image = (&p, &a);
    let listed = |o: &Overlay| {
        let (_, _, table) = list_tsv(&o.types, &o.applied, &[], None, 0, 10);
        table.lines().last().unwrap_or_default().to_owned()
    };
    let define = [(0x1c, "mp", Some("u32")), (0x18, "hp", Some("u32"))];
    let (said, o) =
        state(image, &Overlay::default(), "Player", &define, Mode::Merge).expect("defines");
    assert_eq!(said, "define struct Player: 2 field(s), 0x20 byte(s)");
    let more = [(0x18, "health", None), (0x8, "next", Some("Player *"))];
    let (said, merged) = state(image, &o, "Player", &more, Mode::Merge).expect("merges");
    assert_eq!(
        said,
        "define struct Player: 3 field(s), 0x20 byte(s); 1 kept, 1 changed, 1 new: +0x8 next Player * (new), +0x18 hp u32 -> health u32"
    );
    assert_eq!(
        listed(&merged),
        "struct\tPlayer\t0x20\t0x8 next Player *, 0x18 health u32, 0x1c mp u32"
    );
    let (said, _) = state(
        image,
        &merged,
        "Player",
        &[(0x8, "link", None)],
        Mode::Merge,
    )
    .expect("a name alone keeps the pointer type");
    assert!(
        said.ends_with(": +0x8 next Player * -> link Player *"),
        "{said}"
    );
    let (said, replaced) =
        state(image, &merged, "Player", &define[1..], Mode::Replace).expect("replaces");
    assert_eq!(
        said,
        "define struct Player: 1 field(s), 0x1c byte(s), in place of the 3 it stated"
    );
    assert_eq!(listed(&replaced), "struct\tPlayer\t0x1c\t0x18 hp u32");
    assert_eq!(
        state(image, &o, "Player", &[(0x30, "extra", None)], Mode::Merge)
            .expect_err("a struct's new field needs a type"),
        "field 'extra' at 0x30 states no type, and 'Player' has no field there whose type it could keep"
    );
    let inside = [(0x28, "wide", Some("u64")), (0x26, "half", Some("u32"))];
    assert_eq!(
        state(image, &o, "Player", &inside, Mode::Merge)
            .expect_err("fields stated out of order overlap all the same"),
        "field wide at 0x28 overlaps half at 0x26"
    );
    let roomy = Statement {
        name: "Player",
        size: Some(0x40),
        fields: &[],
        mode: Mode::Merge,
    };
    let mut sized = o.clone();
    plan(&p, &a, &o, &roomy)
        .expect("a size alone")
        .apply(&mut sized);
    let (said, _) = state(image, &sized, "Player", &more[1..], Mode::Merge).expect("merges");
    assert_eq!(
        said,
        "define struct Player: 3 field(s), 0x40 byte(s); 2 kept, 0 changed, 1 new: +0x8 next Player * (new)",
        "a merge without a size keeps the size the struct had"
    );
}

/// A class states no more fields than a struct holds, an overlay those of
/// no more classes than it holds types, and a plan words the first few
/// fields it touches and counts the rest.
#[test]
fn stated_fields_are_capped_and_a_long_plan_counts_its_tail() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let names: Vec<String> = (0..257).map(|k| format!("m_{k}")).collect();
    let fields: Vec<(u64, &str, Option<&str>)> = names
        .iter()
        .zip(0x1000u64..)
        .map(|(name, off)| (off, name.as_str(), None))
        .collect();
    let plain = Overlay::default();
    let (said, _) = state((&p, &a), &plain, CLASS, &fields[..9], Mode::Merge).expect("plans");
    assert!(
        said.starts_with("state 9 field(s) of class class_2800: 6 kept, 0 changed, 9 new: ")
            && said.ends_with(", +0x1007 m_7 (new), +1 more"),
        "{said}"
    );
    assert!(state((&p, &a), &plain, CLASS, &fields[..256], Mode::Merge).is_ok());
    assert_eq!(
        state((&p, &a), &plain, CLASS, &fields, Mode::Merge).expect_err("one field too many"),
        "class class_2800 would state 257 fields, the overlay those of 1 classes; 256 fields of each of 4096 classes are the most"
    );
    let mut full = Overlay::default();
    let others = (0..4095).map(|k| format!("Other{k}"));
    for class in others.chain(["class_2900".to_owned()]) {
        full.fields
            .entry(class)
            .or_default()
            .insert(0, field("m_first", None));
    }
    assert_eq!(
        state((&p, &a), &full, CLASS, &fields[..1], Mode::Merge).expect_err("one class too many"),
        "class class_2800 would state 1 fields, the overlay those of 4097 classes; 256 fields of each of 4096 classes are the most"
    );
    assert!(
        state((&p, &a), &full, "class_2900", &fields[..1], Mode::Merge).is_ok(),
        "a class the overlay states fields of already takes more"
    );
}

/// A statement the class could not print honestly is refused whole.
///
/// One offset stated twice, a name that is no identifier or reads as an
/// unnamed field, one name for two fields, two typed fields over one byte,
/// and the name the class's own asserts give another field.
#[test]
fn a_statement_that_would_not_read_true_is_refused() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let refuse = |fields: &[(u64, &str, Option<&str>)]| {
        state((&p, &a), &o, CLASS, fields, Mode::Merge).expect_err("refused")
    };
    assert_eq!(
        refuse(&[(0x10, "a", None), (0x10, "b", None)]),
        "0x10 is stated twice, as 'a' and 'b'"
    );
    assert_eq!(
        refuse(&[(0x10, "two words", None)]),
        "field name 'two words' is not an identifier"
    );
    assert_eq!(
        refuse(&[(0x10, "field_0x14", None)]),
        "field_0x14 is how an unnamed field prints; give the member's own name"
    );
    assert_eq!(
        refuse(&[(0x10, "m_same", None), (0x14, "m_same", None)]),
        "m_same already names +0x10 of class class_2800; pick another name for +0x14"
    );
    assert_eq!(
        refuse(&[
            (0x10, "m_buf", Some("char[16]")),
            (0x14, "m_in", Some("u32"))
        ]),
        "field m_in at 0x14 overlaps m_buf, which ends at 0x20"
    );
    let fixture = crate::common::fixture();
    let analysis = Analysis::compute(&fixture);
    let of_arr = |fields: &[(u64, &str, Option<&str>)]| {
        state((&fixture, &analysis), &o, "Arr<int>", fields, Mode::Merge)
    };
    assert_eq!(
        of_arr(&[(0x10, "size", None)]).expect_err("the asserts name +0x8 size"),
        "size already names +0x8 of class Arr<int>; pick another name for +0x10"
    );
    let (said, renamed) = of_arr(&[(0x8, "m_size", None)]).expect("the field itself is renamed");
    assert!(said.contains(": +0x8 size -> m_size (accessed "), "{said}");
    assert!(
        of_arr(&[(0x8, "size", None)]).is_ok(),
        "the name the asserts give a field may be stated of that field"
    );
    let over = |fields: &[(u64, &str, Option<&str>)], mode: Mode| {
        state((&fixture, &analysis), &renamed, "Arr<int>", fields, mode)
    };
    assert!(
        over(&[(0x10, "size", None)], Mode::Merge).is_ok(),
        "the name is free while the statement that took its place stays"
    );
    assert_eq!(
        over(&[(0x10, "size", None)], Mode::Replace)
            .expect_err("+0x8 goes by size again once its statement is dropped"),
        "size already names +0x8 of class Arr<int>; pick another name for +0x10"
    );
    assert!(
        over(
            &[(0x8, "m_size", None), (0x10, "size", None)],
            Mode::Replace
        )
        .is_ok(),
        "a replacing statement that restates the field keeps the name free"
    );
    let named = stating(&[(0x18, "m_next", None)]);
    let moved = state(
        (&p, &a),
        &named,
        CLASS,
        &[(0x20, "m_next", None)],
        Mode::Replace,
    );
    assert!(
        moved.is_ok(),
        "a name a replacing statement drops is free: {moved:?}"
    );
}

/// A name is a user struct first, a class borer recovered second and a
/// struct to define last; a statement made of a class outright never
/// lands in a struct of the same name.
#[test]
fn a_name_is_a_struct_before_it_is_a_class() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let fields = [(0x270, "m_currentPipeline", Some("u32"))];
    let (said, as_struct) = state(
        (&p, &a),
        &Overlay::default(),
        "class_28",
        &fields,
        Mode::Merge,
    )
    .expect("defines");
    assert_eq!(said, "define struct class_28: 1 field(s), 0x274 byte(s)");
    assert!(as_struct.fields.is_empty(), "a near miss is no class");
    let mut o = Overlay::default();
    let same_name = plan(
        &p,
        &a,
        &o,
        &Statement {
            name: CLASS,
            size: Some(0x358),
            fields: &[(0x270, field("m_currentPipeline", Some("u32")))],
            mode: Mode::Merge,
        },
    )
    .expect("plans");
    assert_eq!(
        same_name.would(),
        "state 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline u32; a class keeps no stated size"
    );
    assert_eq!(same_name.defined(), None);
    let (_, vec) = state((&p, &a), &o, "Vec", &[(0, "x", Some("f32"))], Mode::Merge).expect("ok");
    o.types.insert(
        CLASS.to_owned(),
        vec.types.get("Vec").cloned().expect("defined"),
    );
    let (said, _) = state((&p, &a), &o, CLASS, &fields, Mode::Merge).expect("merges");
    assert!(
        said.starts_with("define struct class_2800: 2 field(s)"),
        "{said}"
    );
    let statement = Statement {
        name: CLASS,
        size: None,
        fields: &[(0x270, field("m_currentPipeline", None))],
        mode: Mode::Merge,
    };
    let of_class = plan_class(&p, &a, &o, &statement).expect("plans");
    assert!(
        of_class
            .would()
            .starts_with("state 1 field(s) of class class_2800: ")
    );
    assert_eq!(
        plan_class(
            &p,
            &a,
            &o,
            &Statement {
                name: "CLASS_2800",
                ..statement
            }
        )
        .expect_err("a class's name in another case is not its name"),
        "no function belongs to a class named exactly 'CLASS_2800'"
    );
}

/// A field stated at a method lands where stating it by the class's name
/// does, the plan naming the class the method takes its object as.
///
/// That is the class of its `this`, else the class its first parameter is
/// hinted as, else the class its name is qualified by, whose field its own
/// text will not print; a function of no class, and one whose text shows
/// no unnamed field at the offset, say how to state the field by its class.
#[test]
fn a_field_stated_at_a_method_is_stated_of_the_method_s_class() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let fields = [(0x270, "m_currentPipeline", Some("u32"))];
    let (by_name, named) = state((&p, &a), &plain, CLASS, &fields, Mode::Merge).expect("plans");
    let stated = || field("m_currentPipeline", Some("u32"));
    for (entry, found) in [
        (
            0x1000,
            "class_2800::ctor_or_dtor (0x1000) is named after class_2800 and takes its object untyped, so its own text will not print the name: the class's other methods do",
        ),
        (
            0x1040,
            "class_2800::vfunc_0 (0x1040) takes its object as class_2800",
        ),
        (
            0x1080,
            "class_2800::vfunc_1 (0x1080) takes its object as class_2800",
        ),
    ] {
        let at = plan_at(&p, &a, &plain, entry, 0x270, stated()).expect("plans");
        assert_eq!(at.would(), format!("{by_name}; {found}"));
        let mut o = plain.clone();
        at.apply(&mut o);
        assert_eq!(o.fields, named.fields);
        assert_eq!(o.fingerprint(), named.fingerprint());
    }
    let other = plan_at(&p, &a, &plain, OTHER_METHOD, 0x270, stated()).expect("plans");
    assert_eq!(
        other.would(),
        "state 1 field(s) of class class_2900: 3 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline u32; class_2900::vfunc_0 (0x1140) takes its object as class_2900"
    );
    assert_eq!(
        plan_at(&p, &a, &plain, 0x1f00, 0x10, field("m_count", None))
            .expect_err("no function, so no class"),
        "sub_1f00 belongs to no class borer knows, so a field at 0x10 has no class to be stated of; state it by its class, set_type(name=<class>, fields=[\"0x10:m_count\"]), or type the pointer it is read through (borer://layout/0x1f00,apply=<Name> plans that)"
    );
    assert_eq!(
        plan_at(&p, &a, &plain, 0x1040, 0x300, stated())
            .expect_err("the method's text shows no field at 0x300"),
        "class_2800::vfunc_0 (0x1040) names no field_0x300 in its text, so there is no such field to state there; a field the function does not show is stated by its class, set_type(name=class_2800, fields=[\"0x300:m_currentPipeline\"])"
    );
    let mut earlier = stating(&[(0x18, "m_next", None)]);
    let merging = plan_at(&p, &a, &earlier, 0x1080, 0x270, stated()).expect("plans");
    merging.apply(&mut earlier);
    assert_eq!(
        earlier.fields,
        stating(&[(0x18, "m_next", None), fields[0]]).fields,
        "a field stated at a method merges into what the class states"
    );
    let mut renamed = plain;
    renamed.names.insert(0x1040, "draw".to_owned());
    let hinted = plan_at(&p, &a, &renamed, 0x1040, 0x270, stated())
        .expect("plans")
        .would();
    assert!(
        hinted.ends_with("; draw (0x1040) takes its object as class_2800"),
        "a method of no class by its name is of the class its object is hinted as: {hinted}"
    );
    renamed.names.insert(0x1040, "Renderer::draw".to_owned());
    let moved = plan_at(&p, &a, &renamed, 0x1040, 0x270, stated())
        .expect("plans")
        .would();
    assert_eq!(
        moved,
        "state 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline u32; Renderer::draw (0x1040) takes its object as class_2800",
        "a method renamed out of its class still prints its object's fields by that class"
    );
}

/// A method no table hints states a field of the class its `this` is
/// typed as: the class its symbol is qualified by.
#[test]
fn a_field_stated_through_this_is_of_the_class_this_is_typed_as() {
    let (fixture, none) = (crate::common::fixture(), Overlay::default());
    let analysis = Analysis::compute(&fixture);
    let (method, class, unnamed) = analysis
        .functions
        .iter()
        .filter(|f| !f.param_hints.contains_key(&0))
        .find_map(|f| {
            let class = object_class(&analysis, &none, f)?;
            let text = decompile_named(&fixture, &analysis, &none, f.entry)?;
            let shown = "this->field_0x";
            let at = text
                .contains(&format!("{class} *this"))
                .then(|| text.find(shown))??;
            let digits: String = text[at + shown.len()..]
                .chars()
                .take_while(char::is_ascii_hexdigit)
                .collect();
            Some((f.entry, class, u64::from_str_radix(&digits, 16).ok()?))
        })
        .expect("a method no table hints that prints an unnamed field through `this`");
    let through_this = plan_at(
        &fixture,
        &analysis,
        &none,
        method,
        unnamed,
        field("m_stated", None),
    )
    .expect("plans")
    .would();
    assert!(
        through_this.contains(&format!(" of class {class}: "))
            && through_this.ends_with(&format!(" takes its object as {class}")),
        "a method no table hints is of the class its `this` is typed as: {through_this}"
    );
}

/// A layout is planned as a struct under any name but a recovered class's.
///
/// The call such a plan names would state that class's fields; once a
/// user struct goes by the name, the call lands in the struct and the plan
/// stands.
#[test]
fn a_layout_plan_takes_no_recovered_class_s_name() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    assert_eq!(
        from_pointer(&p, &a, &o, "0x1040,rcx", CLASS).expect_err("a class's own name"),
        "class_2800 is a class borer recovered: set_type states that class's fields under its name, so give the struct another name (apply=<Other>)"
    );
    assert!(from_pointer(&p, &a, &o, "0x1040,rcx", "class_2900").is_err());
    let seen = from_pointer(&p, &a, &o, "0x1040,rcx", "Seen").expect("another name plans");
    o.types.insert(CLASS.to_owned(), seen.ty);
    let again = from_pointer(&p, &a, &o, "0x1040,rcx", CLASS);
    assert!(again.is_ok(), "a user struct of the name: {again:?}");
}

/// A type nothing defines is refused with what defines one, and a type
/// named after a recovered class with why stating fields under that name
/// defines no struct.
#[test]
fn an_undefined_type_named_after_a_class_says_why_it_is_no_struct() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let said = |ty: &str, a: Option<&Analysis>| {
        let ty = parse_type(ty).expect("a type the language spells");
        undefined(a, &o, &ty, "define it first")
    };
    let of_class = ": class_2800 is a class borer recovered, and fields stated under that name are the class's, not a struct's; define the struct under another name and apply that";
    for ty in ["class_2800 *", "class_2800[4]", "class_2800"] {
        assert_eq!(
            said(ty, Some(&a)),
            format!("the type {ty} names nothing defined{of_class}")
        );
    }
    for (ty, analysis) in [("Missing *", Some(&a)), ("class_2800 *", None)] {
        assert_eq!(
            said(ty, analysis),
            format!("the type {ty} names nothing defined; define it first")
        );
    }
}

/// The same statements made in another order leave the same overlay, and
/// a fresh analysis prints the same bytes under each.
#[test]
fn statements_in_any_order_leave_one_overlay() {
    let p = two_classes();
    let a = Analysis::compute(&p);
    let first = [(0x270, "m_currentPipeline", Some("u32"))];
    let second = [(0x18, "m_next", None), (0x20, "m_bound", Some("u8"))];
    let plain = Overlay::default();
    let both = |one: &[(u64, &str, Option<&str>)], other: &[(u64, &str, Option<&str>)]| {
        let (_, o) = state((&p, &a), &plain, CLASS, one, Mode::Merge).expect("plans");
        state((&p, &a), &o, CLASS, other, Mode::Merge)
            .expect("plans")
            .1
    };
    let (one_way, other_way) = (both(&first, &second), both(&second, &first));
    assert_eq!(one_way.fingerprint(), other_way.fingerprint());
    let texts = |o: &Overlay| {
        let fresh = Analysis::compute(&p);
        METHODS.map(|entry| decompile_named(&p, &fresh, o, entry))
    };
    assert_eq!(texts(&one_way), texts(&other_way));
    assert!(
        texts(&one_way)[1]
            .as_deref()
            .is_some_and(|text| text.contains("this->m_next") && text.contains("this->m_bound = 1")),
        "{:#?}",
        texts(&one_way)
    );
}
