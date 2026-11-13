//! Tests of the mod SDK over hand-built layouts and SDKs.

use std::collections::{BTreeMap, BTreeSet};

use super::cheat::cheat_table;
use super::header::header;
use super::reclass::{data_xml, reclass, uuid};
use super::{
    Class, Evidence, Field, Global, Sdk, Size, Taken, Ty, build, ident, recovered, unique, xml,
};
use crate::analysis::classes::{ClassLayout, FieldUse};
use crate::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
use crate::analysis::vtables::ClassInfo;
use crate::analysis::{Analysis, Overlay};
use crate::program::{Arch, Program, Section};

/// A program of one `ret`, whose analysis the tests fill with classes.
fn tiny() -> (Program, Analysis) {
    let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
    let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
    let a = Analysis::compute(&p);
    (p, a)
}

/// A field one method accesses at these widths.
fn used(widths: &[u8], reads: usize, writes: usize) -> FieldUse {
    FieldUse {
        widths: widths.iter().copied().collect(),
        reads,
        writes,
        methods: [0x1000].into(),
        ..FieldUse::default()
    }
}

/// A field of the sample.
fn field(off: u64, name: &str, ty: Ty, evidence: Evidence) -> Field {
    Field {
        off,
        name: name.to_owned(),
        ty,
        evidence,
    }
}

/// An SDK of a player with a vtable pointing at a weapon, a stated weapon
/// struct, two globals and a thread-local singleton.
fn sample() -> Sdk {
    let seen = Evidence::Seen {
        reads: 2,
        writes: 1,
        methods: 2,
    };
    let player = Class {
        name: "Demo::Player".to_owned(),
        size: Size::AtLeast(0x30),
        parent: Some("Demo::Actor".to_owned()),
        vtable: Some(0x1_4010_0000),
        slots: vec![
            (0x1_4000_1000, "Demo::Player::~Player".to_owned()),
            (0x1_4000_1100, "Demo::Player::Update".to_owned()),
            (0, "data".to_owned()),
        ],
        fields: vec![
            field(0, "vftable", Ty::VTable, Evidence::Stated),
            field(
                0x10,
                "health",
                Ty::Int {
                    bytes: 4,
                    signed: false,
                },
                seen.clone(),
            ),
            field(0x14, "speed", Ty::Float, seen.clone()),
            field(
                0x20,
                "f_20",
                Ty::Int {
                    bytes: 4,
                    signed: false,
                },
                Evidence::Unsure("accessed 8 and 32 bits wide; the widest is kept".to_owned()),
            ),
            field(
                0x28,
                "weapon",
                Ty::Ptr(Some("Demo::Weapon".to_owned())),
                seen,
            ),
        ],
        notes: vec!["0x18 is only addressed".to_owned()],
    };
    let weapon = Class {
        name: "Demo::Weapon".to_owned(),
        size: Size::Stated(0x18),
        parent: None,
        vtable: None,
        slots: Vec::new(),
        fields: vec![
            field(
                0,
                "ammo",
                Ty::Int {
                    bytes: 4,
                    signed: true,
                },
                Evidence::Stated,
            ),
            field(
                4,
                "name",
                Ty::Bytes(16, "char[16]".to_owned()),
                Evidence::Stated,
            ),
        ],
        notes: Vec::new(),
    };
    Sdk {
        module: "game.exe".to_owned(),
        image_base: 0x1_4000_0000,
        word: 8,
        classes: vec![player, weapon],
        globals: vec![
            Global {
                va: 0x1_4020_0000,
                name: "g_Demo::Player".to_owned(),
                ty: Ty::Ptr(Some("Demo::Player".to_owned())),
                evidence: Evidence::Unsure("a constructor stores its object here".to_owned()),
            },
            Global {
                va: 0x1_4020_0010,
                name: "spare".to_owned(),
                ty: Ty::Bytes(0x18, "Demo::Weapon".to_owned()),
                evidence: Evidence::Stated,
            },
        ],
        tls: vec![(0x10, "Demo::World".to_owned())],
        functions: vec![(0x1_4000_1100, "Demo::Player::Update".to_owned())],
    }
}

/// A recovered layout keeps one field per offset with its evidence.
///
/// The vtable pointer takes offset zero, a field accessed at two widths
/// is unsure and keeps the widest, an embedded object's start is unsure,
/// a pointer the analysis ties to a class points at it, an offset only
/// addressed is a note, and the size is the end of the last field.
///
/// # Panics
///
/// When a field, a note or the size differs.
#[test]
fn a_recovered_layout_keeps_one_field_per_offset_with_its_evidence() {
    let (_, mut a) = tiny();
    let name = "Demo::Player";
    a.classes
        .field_hints
        .insert((name.to_owned(), 0x28), "Demo::Weapon".to_owned());
    a.classes
        .field_types
        .insert((name.to_owned(), 0x30), "Util::Array".to_owned());
    let mut fields = BTreeMap::new();
    fields.insert(0, used(&[64], 0, 2));
    fields.insert(0x10, used(&[32], 2, 1));
    fields.insert(0x14, used(&[8, 32], 1, 1));
    fields.insert(0x16, used(&[16], 1, 0));
    fields.insert(
        0x20,
        FieldUse {
            address_taken: 1,
            ..FieldUse::default()
        },
    );
    fields.insert(0x28, used(&[64], 3, 0));
    fields.insert(0x30, used(&[64], 0, 1));
    let layout = ClassLayout {
        name: name.to_owned(),
        methods: vec![0x1000],
        fields,
        labels: BTreeMap::new(),
        sampled: false,
    };
    let info = ClassInfo {
        name: name.to_owned(),
        vtable: Some(0x5000),
        slots: vec![0x1000],
        parent: Some("Demo::Actor".to_owned()),
        ctors: Vec::new(),
        creators: Vec::new(),
    };
    let c = recovered(name, Some(&layout), Some(&info), &a, &Overlay::default(), 8);
    let got: Vec<(u64, &str, &Ty)> = c
        .fields
        .iter()
        .map(|f| (f.off, f.name.as_str(), &f.ty))
        .collect();
    let u = |bytes| Ty::Int {
        bytes,
        signed: false,
    };
    assert_eq!(
        got,
        [
            (0, "vftable", &Ty::VTable),
            (0x10, "f_10", &u(4)),
            (0x14, "f_14", &u(4)),
            (0x28, "f_28", &Ty::Ptr(Some("Demo::Weapon".to_owned()))),
            (0x30, "f_30", &u(8)),
        ]
    );
    assert_eq!(
        c.fields[1].evidence,
        Evidence::Seen {
            reads: 2,
            writes: 1,
            methods: 1
        }
    );
    assert!(
        matches!(&c.fields[2].evidence, Evidence::Unsure(why) if why.contains("8 and 32 bits")),
        "{:?}",
        c.fields[2]
    );
    assert!(
        matches!(&c.fields[4].evidence, Evidence::Unsure(why) if why.contains("Util::Array")),
        "{:?}",
        c.fields[4]
    );
    assert!(
        c.notes.iter().any(|n| n.contains("0x16 overlaps")),
        "{:?}",
        c.notes
    );
    assert!(
        c.notes.iter().any(|n| n.contains("0x20 is only addressed")),
        "{:?}",
        c.notes
    );
    assert_eq!(c.size, Size::AtLeast(0x38));
    assert_eq!(c.parent.as_deref(), Some("Demo::Actor"));
    assert_eq!(c.slots, [(0x1000, "sub_1000".to_owned())]);
}

/// A struct the overlay states wins over the recovered class of its name.
///
/// It replaces the class's fields but the vtable pointer and sizes it; a
/// global singleton slot becomes a pointer global, and a name the overlay
/// gives a data address a global of it.
///
/// # Panics
///
/// When the built SDK differs.
#[test]
fn a_stated_struct_wins_over_the_recovered_class_of_its_name() {
    let (p, mut a) = tiny();
    for (name, vtable) in [("Player", 0x5000), ("Tiny", 0x5100)] {
        let info = ClassInfo {
            name: name.to_owned(),
            vtable: Some(vtable),
            slots: Vec::new(),
            parent: None,
            ctors: Vec::new(),
            creators: Vec::new(),
        };
        a.classes.by_name.insert(name.to_owned(), info);
    }
    a.classes.global_hints.insert(0x6000, "Player".to_owned());
    let mut o = Overlay::default();
    let four = UserStruct {
        size: 4,
        fields: BTreeMap::new(),
    };
    o.types.insert("Tiny".to_owned(), UserType::Struct(four));
    let fields = [
        (
            8,
            UserField {
                name: "hp".to_owned(),
                ty: TypeExpr::I32,
            },
        ),
        (
            0x10,
            UserField {
                name: "target".to_owned(),
                ty: TypeExpr::Ptr(Box::new(TypeExpr::Named("Player".to_owned()))),
            },
        ),
    ];
    o.types.insert(
        "Player".to_owned(),
        UserType::Struct(UserStruct {
            size: 0x20,
            fields: fields.into_iter().collect(),
        }),
    );
    o.names.insert(0x6008, "g_frame".to_owned());
    let handle = TypeExpr::Ptr(Box::new(TypeExpr::Named("Player".to_owned())));
    o.types.insert("Handle".to_owned(), UserType::Alias(handle));
    o.applied
        .insert(0x6010, TypeExpr::Named("Handle".to_owned()));
    let sdk = build(&p, &a, &o);
    let player = sdk.class("Player").expect("built");
    assert_eq!(player.size, Size::Stated(0x20));
    assert_eq!(player.vtable, Some(0x5000));
    let names: Vec<&str> = player.fields.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(
        names,
        ["vftable", "hp", "target"],
        "the vtable pointer stays"
    );
    assert_eq!(
        player.fields[1].ty,
        Ty::Int {
            bytes: 4,
            signed: true
        }
    );
    assert_eq!(player.fields[2].ty, Ty::Ptr(Some("Player".to_owned())));
    let globals: Vec<(u64, &str)> = sdk
        .globals
        .iter()
        .map(|g| (g.va, g.name.as_str()))
        .collect();
    assert_eq!(
        globals,
        [
            (0x6000, "g_Player"),
            (0x6008, "g_frame"),
            (0x6010, "g_6010")
        ]
    );
    assert_eq!(sdk.globals[0].ty, Ty::Ptr(Some("Player".to_owned())));
    assert_eq!(
        sdk.globals[2].ty,
        Ty::Ptr(Some("Player".to_owned())),
        "an alias of a pointer is the pointer"
    );
    let tiny = sdk.class("Tiny").expect("built");
    assert!(
        tiny.fields.is_empty(),
        "a stated struct smaller than a pointer has no room for the vtable pointer"
    );
    assert_eq!(sdk.module, "module");
    assert_eq!(build(&p, &a, &o), sdk, "the same inputs build the same SDK");
}

/// The header lays each class out exactly.
///
/// It pads between the fields, asserts each offset and the size, writes
/// the vtable as a struct of its slots, says which fields are unsure, and
/// gives the addresses relative to the base.
///
/// # Panics
///
/// When a line of the header differs.
#[test]
fn the_header_lays_classes_out_with_asserts_and_addresses() {
    let mut odd = sample();
    odd.module = "a\"b*/c.exe".to_owned();
    if let Some(slot) = odd.classes.get_mut(0).and_then(|c| c.slots.get_mut(2)) {
        slot.1 = "Demo_Player_vftable".to_owned();
    }
    let h = header(&odd);
    assert!(h.contains(" * Mod SDK for a\"b* /c.exe (64-bit)"), "{h}");
    assert!(
        h.contains("    void* Demo_Player_vftable_2; /* [2]"),
        "a slot is not named like its struct: {h}"
    );
    assert_eq!(
        h.matches("a\"b").count(),
        1,
        "the name is in the comment alone"
    );
    let h = header(&sdk_checked());
    for line in [
        "#pragma once",
        "static_assert(sizeof(void*) == 8, \"the module is a 64-bit image\");",
        "struct Demo_Player;\nstruct Demo_Player_vftable;\nstruct Demo_Weapon;\n",
        "#pragma pack(push, 1)",
        "struct Demo_Player_vftable {\n    void* Player; /* [0] rva 0x1000 Demo::Player::~Player */\n    void* Update; /* [1] rva 0x1100 Demo::Player::Update */\n    void* data; /* [2] a data word, not a function */\n};",
        "/* Demo::Player; parent Demo::Actor; vtable rva 0x100000; size at least 0x30 (the end of the last field seen)\n   note: 0x18 is only addressed */",
        "struct Demo_Player {\n    ::sdk::Demo_Player_vftable* vftable; /* +0x0 */\n    std::uint8_t pad_8[0x8];\n    std::uint32_t health; /* +0x10 recovered: reads 2, writes 1, methods 2 */\n    float speed; /* +0x14 recovered: reads 2, writes 1, methods 2 */\n    std::uint8_t pad_18[0x8];\n    std::uint32_t f_20; /* +0x20 unsure: accessed 8 and 32 bits wide; the widest is kept */\n    std::uint8_t pad_24[0x4];\n    ::sdk::Demo_Weapon* weapon; /* +0x28 recovered: reads 2, writes 1, methods 2 */\n};",
        "static_assert(offsetof(Demo_Player, weapon) == 0x28, \"Demo_Player::weapon\");",
        "static_assert(sizeof(Demo_Player) == 0x30, \"Demo_Player size\");",
        "struct Demo_Weapon {\n    std::int32_t ammo; /* +0x0 */\n    std::uint8_t name[0x10]; /* +0x4 char[16] */\n    std::uint8_t pad_14[0x4];\n};",
        "static_assert(sizeof(Demo_Weapon) == 0x18, \"Demo_Weapon size\");",
        "#pragma pack(pop)",
        "namespace rva {\nconstexpr std::uintptr_t Demo_Player_vftable = 0x100000;\nconstexpr std::uintptr_t Demo_Player_Update = 0x1100; /* Demo::Player::Update */\n}",
        "constexpr std::uintptr_t g_Demo_Player = 0x200000; /* Demo::Player *: unsure: a constructor stores its object here */",
        "constexpr std::uintptr_t spare = 0x200010; /* Demo::Weapon: stated */",
        "constexpr std::uintptr_t Demo_World = 0x10;",
        "} // namespace sdk\n",
    ] {
        assert!(h.contains(line), "missing {line:?} in\n{h}");
    }
}

/// The sample, checked to be what the tests mean it to be.
///
/// # Panics
///
/// When the sample's weapon is not the two fields the tests read.
fn sdk_checked() -> Sdk {
    let s = sample();
    assert_eq!(s.class("Demo::Weapon").map(|c| c.fields.len()), Some(2));
    s
}

/// The Cheat Engine table follows each singleton into its fields.
///
/// A global sits at `"module"+rva`: a pointer to a class is a group CE
/// follows with one zero offset, its fields children at `+offset` typed
/// as CE types them; a struct in place is a group without the offset, and
/// an unsure field says so.
///
/// # Panics
///
/// When a record differs.
#[test]
fn the_cheat_table_follows_singletons_into_their_fields() {
    let t = cheat_table(&sample());
    assert!(t.starts_with("<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<CheatTable CheatEngineTableVersion=\"45\">"), "{t}");
    for part in [
        "<ID>0</ID>\n      <Description>\"g_Demo::Player -&gt; Demo::Player [unsure: a constructor stores its object here]\"</Description>\n      <Options moHideChildren=\"1\"/>\n      <GroupHeader>1</GroupHeader>\n      <Address>\"game.exe\"+200000</Address>\n      <Offsets>\n        <Offset>0</Offset>\n      </Offsets>",
        "<ID>1</ID>\n          <Description>\"vftable\"</Description>\n          <VariableType>8 Bytes</VariableType>\n          <ShowAsHex>1</ShowAsHex>\n          <Address>+0</Address>",
        "<Description>\"health\"</Description>\n          <VariableType>4 Bytes</VariableType>\n          <Address>+10</Address>",
        "<Description>\"speed\"</Description>\n          <VariableType>Float</VariableType>\n          <Address>+14</Address>",
        "<Description>\"f_20 [unsure: accessed 8 and 32 bits wide; the widest is kept]\"</Description>",
        "<Description>\"weapon -&gt; Demo::Weapon\"</Description>\n          <VariableType>8 Bytes</VariableType>\n          <ShowAsHex>1</ShowAsHex>\n          <Address>+28</Address>",
        "<Description>\"spare (Demo::Weapon)\"</Description>\n      <Options moHideChildren=\"1\"/>\n      <GroupHeader>1</GroupHeader>\n      <Address>\"game.exe\"+200010</Address>\n      <CheatEntries>",
        "<Description>\"ammo\"</Description>\n          <VariableType>4 Bytes</VariableType>\n          <ShowAsSigned>1</ShowAsSigned>\n          <Address>+0</Address>",
        "<Description>\"name (char[16])\"</Description>\n          <VariableType>Array of byte</VariableType>\n          <ByteLength>16</ByteLength>\n          <Address>+4</Address>",
        "Thread-local singleton Demo::World: offset 0x10",
        "</Comments>\n</CheatTable>\n",
    ] {
        assert!(t.contains(part), "missing {part:?} in\n{t}");
    }
    let ids: Vec<&str> = t
        .split("<ID>")
        .skip(1)
        .filter_map(|s| s.split("</ID>").next())
        .collect();
    let distinct: BTreeSet<&str> = ids.iter().copied().collect();
    assert_eq!(distinct.len(), ids.len(), "ids are unique: {ids:?}");
    assert_eq!(ids.len(), 9, "two groups and their seven fields");
}

/// The ReClass.NET project places every field by the nodes before it.
///
/// Hex nodes fill each gap, the vtable lists its slots, a pointer to a
/// class the SDK lays out references that class's uuid, and a singleton's
/// class takes the global as its address.
///
/// # Panics
///
/// When a node differs.
#[test]
fn the_reclass_project_places_fields_by_the_nodes_before_them() {
    let x = data_xml(&sample());
    let weapon = uuid("Demo::Weapon");
    for part in [
        "<reclass version=\"65537\" type=\"x64\">\n  <classes>\n".to_owned(),
        format!("<class uuid=\"{}\" name=\"Demo::Player\" comment=\"parent Demo::Actor (its fields are flattened in); size at least 0x30; 0x18 is only addressed\" address=\"[&lt;game.exe&gt; + 200000]\">", uuid("Demo::Player")),
        "<node type=\"VirtualMethodTableNode\" name=\"vftable\" comment=\"\" hidden=\"false\">\n        <method name=\"Demo::Player::~Player\" comment=\"\" hidden=\"false\" />\n        <method name=\"Demo::Player::Update\" comment=\"\" hidden=\"false\" />\n        <method name=\"data\" comment=\"\" hidden=\"false\" />\n      </node>\n      <node type=\"Hex64Node\" name=\"\" comment=\"\" hidden=\"false\" />\n      <node type=\"UInt32Node\" name=\"health\"".to_owned(),
        "<node type=\"FloatNode\" name=\"speed\"".to_owned(),
        "<node type=\"UInt32Node\" name=\"f_20\" comment=\"unsure: accessed 8 and 32 bits wide; the widest is kept\" hidden=\"false\" />\n      <node type=\"Hex32Node\" name=\"\" comment=\"\" hidden=\"false\" />\n      <node type=\"PointerNode\" name=\"weapon\"".to_owned(),
        format!("<node type=\"ClassInstanceNode\" name=\"\" comment=\"\" hidden=\"false\" reference=\"{weapon}\" />"),
        format!("<class uuid=\"{weapon}\" name=\"Demo::Weapon\" comment=\"size 0x18 (stated)\" address=\"&lt;game.exe&gt; + 200010\">\n      <node type=\"Int32Node\" name=\"ammo\" comment=\"\" hidden=\"false\" />\n      <node type=\"Hex64Node\" name=\"name\" comment=\"char[16]\" hidden=\"false\" />\n      <node type=\"Hex64Node\" name=\"\" comment=\"\" hidden=\"false\" />\n      <node type=\"Hex32Node\" name=\"\" comment=\"\" hidden=\"false\" />\n    </class>"),
    ] {
        assert!(x.contains(&part), "missing {part:?} in\n{x}");
    }
}

/// A struct the overlay states a gigabyte long stops its nodes at the gap
/// no project spells in hex nodes, and says where.
///
/// # Panics
///
/// When the nodes run on or the class does not say where they stop.
#[test]
fn a_huge_gap_stops_a_reclass_class_and_says_where() {
    let mut sdk = sample();
    let weapon = sdk.classes.get_mut(1).expect("the weapon");
    weapon.size = Size::Stated(0x4000_0000);
    let x = data_xml(&sdk);
    assert!(
        x.contains("; the nodes stop at +0x14, where 0x3fffffec bytes run past the 0x10000 a project spells in hex nodes\""),
        "{x}"
    );
    assert!(x.len() < 8192, "{} bytes", x.len());
}

/// The project is a zip of one stored `Data.xml` whose sizes, offsets and
/// CRC agree with the XML, as a zip reader checks them.
///
/// # Panics
///
/// When a header field disagrees.
#[test]
fn the_reclass_file_is_a_stored_zip_of_data_xml() {
    let sdk = sample();
    let zip = reclass(&sdk).expect("fits");
    let xml = data_xml(&sdk);
    let u16_at = |i: usize| u16::from_le_bytes([zip[i], zip[i + 1]]);
    let u32_at = |i: usize| u32::from_le_bytes([zip[i], zip[i + 1], zip[i + 2], zip[i + 3]]);
    let n = xml.len();
    assert_eq!(u32_at(0), 0x0403_4b50);
    assert_eq!(u16_at(8), 0, "stored");
    assert_eq!(u32_at(14), crate::carve::crc32(xml.as_bytes()));
    assert_eq!(usize::try_from(u32_at(18)).ok(), Some(n));
    assert_eq!(&zip[30..38], b"Data.xml");
    assert_eq!(&zip[38..38 + n], xml.as_bytes());
    let central = 38 + n;
    assert_eq!(u32_at(central), 0x0201_4b50);
    assert_eq!(u32_at(central + 42), 0, "the entry starts the file");
    let end = central + 46 + 8;
    assert_eq!(zip.len(), end + 22);
    assert_eq!(u32_at(end), 0x0605_4b50);
    assert_eq!(u16_at(end + 10), 1, "one entry");
    assert_eq!(usize::try_from(u32_at(end + 12)).ok(), Some(54));
    assert_eq!(usize::try_from(u32_at(end + 16)).ok(), Some(central));
}

/// A uuid is a name-based GUID: the same for a name, other for another,
/// spelled as ReClass.NET parses it.
///
/// # Panics
///
/// When a uuid repeats or is misspelled.
#[test]
fn a_class_uuid_is_its_names_and_spelled_as_a_guid() {
    let a = uuid("Demo::Player");
    assert_eq!(a, uuid("Demo::Player"));
    assert_ne!(a, uuid("Demo::Weapon"));
    let groups: Vec<usize> = a.split('-').map(str::len).collect();
    assert_eq!(groups, [8, 4, 4, 4, 12], "{a}");
    assert_eq!(a.as_bytes()[14], b'5', "version 5: {a}");
    assert!(matches!(a.as_bytes()[19], b'8' | b'9' | b'a' | b'b'), "{a}");
}

/// A name becomes an identifier a C++ compiler takes, and two names that
/// meet in one become two.
///
/// # Panics
///
/// When an identifier differs.
#[test]
fn names_become_distinct_cpp_identifiers() {
    assert_eq!(
        ident("Util::Array<Lib::Ref<UI::Icon> >"),
        "Util_Array_Lib_Ref_UI_Icon"
    );
    assert_eq!(ident("`vftable'"), "vftable");
    assert_eq!(ident("~Player"), "Player");
    assert_eq!(ident("3d"), "n_3d");
    assert_eq!(ident("::"), "n_");
    assert_eq!(ident("delete"), "delete_");
    assert_eq!(ident("NULL"), "NULL_");
    assert_eq!(ident("UINT64_MAX"), "UINT64_MAX_");
    assert_eq!(ident("INT8_C"), "INT8_C_");
    assert_eq!(ident("MAX_HP"), "MAX_HP");
    let mut taken = Taken::default();
    assert_eq!(unique(&mut taken, "a"), "a");
    assert_eq!(unique(&mut taken, "a"), "a_2");
    assert_eq!(unique(&mut taken, "a"), "a_3");
}

/// XML text keeps every character an address may name, a module's
/// non-ASCII name included, escapes the markup and drops control
/// characters XML cannot hold.
///
/// # Panics
///
/// When the text differs.
#[test]
fn xml_text_keeps_a_unicode_module_name() {
    assert_eq!(
        xml("\"café.exe\"+10 <a&b>\u{1}"),
        "&quot;café.exe&quot;+10 &lt;a&amp;b&gt;?"
    );
    let mut sdk = sample();
    sdk.module = "café.exe".to_owned();
    assert!(cheat_table(&sdk).contains("<Address>\"café.exe\"+200000</Address>"));
}

/// Returns the sample SDK with its weapon class stating 256 runs of
/// 0xffff bytes, just under the longest run a class spells.
fn wide_runs() -> Sdk {
    let mut sdk = sample();
    if let Some(wide) = sdk.classes.get_mut(1) {
        let bytes = || Ty::Bytes(0xffff, "u8[65535]".to_owned());
        wide.fields = (0..256u64)
            .map(|k| field(k << 16, &format!("f{k}"), bytes(), Evidence::Stated))
            .collect();
        wide.size = Size::Stated(256 << 16);
    }
    sdk
}

/// A class's runs of hex nodes stop where its budget is spent, and say
/// so: 256 runs just under the longest a class spells were two million
/// nodes for the one class.
///
/// # Panics
///
/// When the nodes run past the budget or the class does not say where
/// they stop.
#[test]
fn a_reclass_project_spends_at_most_its_hex_nodes() {
    let x = data_xml(&wide_runs());
    let hex = x.matches("<node type=\"Hex").count();
    assert!(hex <= 1 << 16, "{hex} hex nodes");
    assert!(
        x.contains(
            "the nodes stop at +0x70000, where the 0x10000 hex nodes a class spells are spent"
        ),
        "{}",
        x.get(..4096).unwrap_or(&x)
    );
}

/// Each class of a ReClass.NET project spends its own hex nodes, so the
/// last of 1,100 classes keeps the field after its first gap.
///
/// The budget was the project's: past about the 1,024th class of 0x200
/// unknown bytes, a class lost every field after its first gap, while the
/// export still counted them.
///
/// # Panics
///
/// When the last class's field is missing.
#[test]
fn each_reclass_class_spends_its_own_hex_nodes() {
    let mut sdk = sample();
    let int = Ty::Int {
        bytes: 8,
        signed: false,
    };
    let template = sdk.classes.get(1).cloned().expect("the weapon");
    sdk.classes = (0..1100)
        .map(|k| Class {
            name: format!("C{k:04}"),
            size: Size::Stated(0x208),
            fields: vec![field(0x200, "q", int.clone(), Evidence::Stated)],
            ..template.clone()
        })
        .collect();
    let x = data_xml(&sdk);
    let last = x.rsplit("<class ").next().unwrap_or_default();
    assert!(last.contains("name=\"C1099\""), "{last}");
    assert!(
        last.contains("<node type=\"UInt64Node\" name=\"q\""),
        "{last}"
    );
}

/// A ReClass.NET project whose XML passes the bytes a mod file holds is
/// refused before it is zipped: the cut XML was zipped and checksummed,
/// and only the zip's size refused it.
///
/// # Panics
///
/// When the project is zipped, or the refusal does not name the cap.
#[test]
fn a_reclass_project_past_the_cap_is_refused_before_it_is_zipped() {
    let mut sdk = wide_runs();
    let template = sdk.classes.get(1).cloned().expect("the weapon");
    sdk.classes = (0..24)
        .map(|k| Class {
            name: format!("W{k:02}"),
            ..template.clone()
        })
        .collect();
    let refused = reclass(&sdk).expect_err("a project past the cap was zipped");
    assert!(
        refused
            .to_string()
            .starts_with("the ReClass.NET project passes the 67108864 bytes a mod file holds"),
        "{refused}"
    );
}

/// A Cheat Engine table past the bytes a mod file holds stops at the
/// global that took it past them, and is refused rather than written.
///
/// Two thousand globals of a class of 256 fields were a hundred MiB of
/// entries.
///
/// # Panics
///
/// When the table runs on past the cap, or one past it is accepted.
#[test]
fn a_mod_file_past_its_cap_is_cut_and_refused() {
    let mut sdk = sample();
    let weapon = sdk.classes.get_mut(1).expect("the weapon");
    let int = || Ty::Int {
        bytes: 4,
        signed: false,
    };
    weapon.fields = (0..256u64)
        .map(|k| field(k * 4, &format!("f{k}"), int(), Evidence::Stated))
        .collect();
    weapon.size = Size::Stated(0x400);
    sdk.globals = (0..2000u64)
        .map(|k| Global {
            va: 0x1_4020_0000 + k * 0x400,
            name: format!("g{k}"),
            ty: Ty::Bytes(0x400, "Demo::Weapon".to_owned()),
            evidence: Evidence::Stated,
        })
        .collect();
    let table = cheat_table(&sdk);
    assert!(
        table.len() <= super::FILE_MAX + (1 << 17),
        "{} bytes",
        table.len()
    );
    let refused = super::fits(&sdk, "Cheat Engine table", table.into_bytes())
        .expect_err("a table past the cap");
    assert!(
        refused
            .to_string()
            .starts_with("the Cheat Engine table passes the 67108864 bytes a mod file holds"),
        "{refused}"
    );
    assert!(super::fits(&sdk, "header", header(&sample()).into_bytes()).is_ok());
}

/// Each renderer stops before its next class or global once the caller's
/// flag is raised, so a request past its deadline renders nothing more.
///
/// # Panics
///
/// When a renderer goes on under the raised flag, or stops without it.
#[test]
fn the_mod_files_stop_rendering_once_the_flag_is_raised() {
    let sdk = sample();
    let flag = crate::cancel::Cancel::new();
    flag.raise();
    let (h, t, x) = flag.within(|| (header(&sdk), cheat_table(&sdk), data_xml(&sdk)));
    assert!(!h.contains("struct Demo_Player {"), "{h}");
    assert!(!t.contains("<CheatEntry>"), "{t}");
    assert!(!x.contains("<class "), "{x}");
    assert!(header(&sdk).contains("struct Demo_Player {"));
}

/// The rows after the classes stop once the caller's flag is raised too.
///
/// They are the header's forward declarations and address rows, and the
/// table's thread-local singletons: a binary naming functions by the
/// million rendered their rows on past the cap after its last class.
///
/// # Panics
///
/// When a row renders under the raised flag, or none renders without it.
#[test]
fn the_rows_after_the_classes_stop_once_the_flag_is_raised() {
    let sdk = sample();
    let flag = crate::cancel::Cancel::new();
    flag.raise();
    let (h, t) = flag.within(|| (header(&sdk), cheat_table(&sdk)));
    let rows = ["struct Demo_Player;", "constexpr std::uintptr_t"];
    assert!(rows.iter().all(|row| !h.contains(row)), "{h}");
    assert!(!t.contains("Thread-local singleton"), "{t}");
    let (h, t) = (header(&sdk), cheat_table(&sdk));
    assert!(rows.iter().all(|row| h.contains(row)), "{h}");
    assert!(t.contains("Thread-local singleton"), "{t}");
}

/// A header of 131,072 globals all named `x` names them in linear time.
///
/// Each `x` tried every suffix from 2 up: nine billion tries, hours of an
/// export.
///
/// # Panics
///
/// When the header takes over ten seconds, or its last global is not
/// `x_131072`.
#[test]
fn many_globals_of_one_name_are_named_in_linear_time() {
    let mut sdk = sample();
    sdk.globals = (0..1u64 << 17)
        .map(|k| Global {
            va: 0x1_4020_0000 + k * 8,
            name: "x".to_owned(),
            ty: Ty::Int {
                bytes: 8,
                signed: false,
            },
            evidence: Evidence::Stated,
        })
        .collect();
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || tx.send(header(&sdk)));
    let h = rx
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("the header is written within ten seconds");
    assert!(
        h.contains("constexpr std::uintptr_t x_131072 = "),
        "{} bytes",
        h.len()
    );
}

/// [`data_xml`] indexes the globals once before rendering the classes, so
/// 4,096 classes alongside 100,000 integer globals render in linearithmic
/// time and still take the singleton address of `C0`.
///
/// # Panics
///
/// When [`data_xml`] takes over ten seconds, or `C0` lacks its singleton
/// address.
#[test]
fn many_classes_and_scalar_globals_render_reclass_xml_without_rescanning() {
    let mut sdk = sample();
    sdk.classes = (0..4096)
        .map(|k| Class {
            name: format!("C{k}"),
            size: Size::Stated(8),
            parent: None,
            vtable: None,
            slots: Vec::new(),
            fields: Vec::new(),
            notes: Vec::new(),
        })
        .collect();
    sdk.classes.sort_by(|a, b| a.name.cmp(&b.name));
    sdk.globals = (0..100_000u64)
        .map(|k| Global {
            va: 0x1_4020_0000 + k * 4,
            name: format!("g{k}"),
            ty: Ty::Int {
                bytes: 4,
                signed: false,
            },
            evidence: Evidence::Stated,
        })
        .chain(std::iter::once(Global {
            va: 0x1_4099_9900,
            name: "g_c0".to_owned(),
            ty: Ty::Ptr(Some("C0".to_owned())),
            evidence: Evidence::Stated,
        }))
        .collect();
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || tx.send(data_xml(&sdk)));
    let rendered = rx
        .recv_timeout(std::time::Duration::from_secs(10))
        .expect("reclass XML renders within ten seconds");
    let expected = format!(
        "name=\"C0\" comment=\"size 0x8 (stated)\" address=\"{}\"",
        xml("[<game.exe> + 999900]")
    );
    assert!(rendered.contains(&expected), "{} bytes", rendered.len());
}

/// [`super::fits`] refuses a cancelled render even when it fits [`super::FILE_MAX`].
///
/// # Panics
///
/// When a cancelled render passes [`super::fits`] or a whole render fails.
#[test]
fn fits_refuses_a_cancelled_render_under_the_cap() {
    let sdk = sample();
    let flag = crate::cancel::Cancel::new();
    flag.raise();
    let (h, ct) = flag.within(|| {
        (
            super::fits(&sdk, "C++ header", header(&sdk).into_bytes()),
            super::fits(&sdk, "Cheat Engine table", cheat_table(&sdk).into_bytes()),
        )
    });
    assert!(h.is_err_and(|e| e.to_string().contains("deadline passed")));
    assert!(ct.is_err_and(|e| e.to_string().contains("deadline passed")));
    assert!(super::fits(&sdk, "C++ header", header(&sdk).into_bytes()).is_ok());
}
