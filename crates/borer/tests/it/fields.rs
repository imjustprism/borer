//! Fields stated of a class, over JSON-RPC stdio on the real binary
//! (`CARGO_BIN_EXE_borer`).
//!
//! `set_type` states one by the class's name or at a method and keeps the
//! rest, a project keeps them, and every answer that lists a class's
//! fields shows them.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
#![expect(
    clippy::expect_used,
    reason = "a fixture that cannot be written or read has no useful recovery in a test"
)]

use std::path::PathBuf;

use borer::project::{ProjectFile, identity};
use borer_engine::analysis::Overlay;
use borer_engine::analysis::stated::Field;
use borer_engine::analysis::utypes::parse_type;

use crate::contract::tiny_pe;
use crate::reload::Client;
use crate::resources::read;
use crate::without_evidence;

/// How `load_binary` maps [`two_classes`]: code at 0x1000, tables at 0x2000.
const REGIONS: &str = "0x1000@0:0x1000:rx,0x2000@0x1000:0x1000:r";

/// Writes hex bytes into an image mapped at 0x1000.
///
/// # Arguments
///
/// * `image` - The image.
/// * `va` - Where the bytes go.
/// * `hex` - The bytes, as hex pairs apart.
fn put(image: &mut [u8], va: usize, hex: &str) {
    for (k, byte) in hex.split_whitespace().enumerate() {
        image[va - 0x1000 + k] = u8::from_str_radix(byte, 16).expect("a hex pair");
    }
}

/// A raw x86-64 image of two classes nothing names and one free function.
///
/// `class_2800` (table at 0x2800) is built at 0x1000 (`lea rax, [table];
/// mov [rcx], rax; mov dword [rcx+0x270], -1; ret`) and has the methods
/// 0x1040 (`mov eax, [rcx+0x270]; add eax, [rcx+0x10]; mov [rcx+0x14],
/// eax; ret`) and 0x1080 (`mov [rcx+0x270], edx; mov rax, [rcx+0x18]; mov
/// byte [rcx+0x20], 1; ret`). `class_2900` (table at 0x2900) is built at
/// 0x1100 and has 0x1140 (`mov eax, [rcx+0x270]; add eax, [rcx+0x30]; mov
/// [rcx+0x34], eax; ret`) and 0x1180 (`mov eax, [rcx+0x30]; ret`). 0x11c0
/// (`mov eax, [rcx+0x10]; add eax, [rcx+0x14]; add eax, [rcx+0x18]; ret`)
/// belongs to no class; a pointer at 0x2a00 seeds it, as one after each
/// table seeds its constructor.
fn two_classes() -> Vec<u8> {
    let mut image = vec![0xccu8; 0x2000];
    let table = "48 8d 05 f9 17 00 00 48 89 01";
    put(&mut image, 0x1000, table);
    put(&mut image, 0x100a, "c7 81 70 02 00 00 ff ff ff ff c3");
    put(&mut image, 0x1040, "8b 81 70 02 00 00 03 41 10 89 41 14 c3");
    put(
        &mut image,
        0x1080,
        "89 91 70 02 00 00 48 8b 41 18 c6 41 20 01 c3",
    );
    put(&mut image, 0x1100, table);
    put(&mut image, 0x110a, "c3");
    put(&mut image, 0x1140, "8b 81 70 02 00 00 03 41 30 89 41 34 c3");
    put(&mut image, 0x1180, "8b 41 30 c3");
    put(&mut image, 0x11c0, "8b 41 10 03 41 14 03 41 18 c3");
    for (at, target) in [
        (0x2800, 0x1040u64),
        (0x2808, 0x1080),
        (0x2818, 0x1000),
        (0x2900, 0x1140),
        (0x2908, 0x1180),
        (0x2918, 0x1100),
        (0x2a00, 0x11c0),
    ] {
        image[at - 0x1000..at - 0x1000 + 8].copy_from_slice(&target.to_le_bytes());
    }
    for at in [0x2810, 0x2910] {
        image[at - 0x1000..at - 0x1000 + 8].fill(0);
    }
    image
}

/// A session with [`two_classes`] loaded, and the directory its files are
/// in.
///
/// # Arguments
///
/// * `tag` - A name of the test's own, for the directory.
///
/// # Returns
///
/// The session, the directory to remove afterwards, and the image's path.
fn session(tag: &str) -> (Client, PathBuf, String) {
    let dir = std::env::temp_dir().join(format!("borer-fields-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a directory of the test's own");
    let (start, image) = (dir.join("start.exe"), dir.join("classes.bin"));
    std::fs::write(&start, tiny_pe()).expect("the fixture is writable");
    std::fs::write(&image, two_classes()).expect("the fixture is writable");
    let mut client = Client::start(&start.to_string_lossy());
    let path = image.to_string_lossy().into_owned();
    let load = serde_json::json!({"path": path, "arch": "x64", "regions": REGIONS});
    let loaded = client.text("load_binary", &load.to_string());
    assert!(loaded.contains("image:   kind stated layout"), "{loaded}");
    (client, dir, path)
}

/// The rows of a class's layout, one per field.
///
/// # Arguments
///
/// * `client` - The session.
/// * `class` - The class.
fn rows(client: &mut Client, class: &str) -> Vec<String> {
    let layout = client.text(
        "class_layout",
        &serde_json::json!({"class": class}).to_string(),
    );
    layout
        .lines()
        .filter(|l| l.starts_with('+'))
        .map(str::to_owned)
        .collect()
}

/// A function's text, whole.
///
/// # Arguments
///
/// * `client` - The session.
/// * `address` - The function.
fn text_of(client: &mut Client, address: &str) -> String {
    let args = serde_json::json!({"address": address, "limit": 100_000});
    without_evidence(&client.text("decompile", &args.to_string())).to_owned()
}

/// The fields stated of classes survive a save and a load, field for
/// field, and a project that states none writes no table.
#[test]
fn stated_fields_round_trip_through_json() {
    let mut o = Overlay::default();
    let fields = o.fields.entry("Ns::Thing<int>".to_owned()).or_default();
    fields.insert(
        0x270,
        Field {
            name: "m_currentPipeline".to_owned(),
            ty: Some(parse_type("Pipeline *").expect("a type")),
        },
    );
    fields.insert(
        0x18,
        Field {
            name: "m_next".to_owned(),
            ty: None,
        },
    );
    let pf = ProjectFile::from_overlay("bin", None, &o);
    assert_eq!(
        serde_json::to_value(&pf.fields).expect("serializes"),
        serde_json::json!({"Ns::Thing<int>": {"0x18": "m_next", "0x270": "m_currentPipeline Pipeline *"}})
    );
    let refused = pf
        .to_overlay()
        .expect_err("Pipeline is no type the project states");
    assert_eq!(
        refused,
        "field m_currentPipeline's type Pipeline * resolves to no size at 0x270"
    );
    let dir = std::env::temp_dir().join(format!("borer-fields-json-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a directory of the test's own");
    let path = dir.join("fields.json");
    let typed = serde_json::json!({
        "program": "bin", "names": {}, "comments": {},
        "fields": {"Ns::Thing<int>": {"0x18": "m_next", "624": "m_currentPipeline u8 *"}}
    });
    std::fs::write(&path, typed.to_string()).expect("the project is writable");
    let loaded = ProjectFile::load(&path.to_string_lossy())
        .and_then(|pf| pf.to_overlay())
        .expect("loads");
    let spelled: Vec<(u64, String)> = loaded
        .fields
        .get("Ns::Thing<int>")
        .into_iter()
        .flatten()
        .map(|(off, field)| (*off, field.spell()))
        .collect();
    assert_eq!(
        spelled,
        [
            (0x18, "m_next".to_owned()),
            (0x270, "m_currentPipeline u8 *".to_owned())
        ]
    );
    let again = ProjectFile::from_overlay("bin", None, &loaded)
        .to_overlay()
        .expect("loads");
    assert_eq!(again.fingerprint(), loaded.fingerprint());
    assert_ne!(loaded.fingerprint(), Overlay::default().fingerprint());
    let plain = serde_json::to_string(&ProjectFile::from_overlay("bin", None, &Overlay::default()))
        .expect("serializes");
    assert!(!plain.contains("fields"), "{plain}");
    std::fs::remove_dir_all(&dir).ok();
}

/// A hand-edited project whose stated fields could not be printed
/// honestly is refused with a message naming the field.
#[test]
fn a_hostile_project_refuses_its_stated_fields() {
    let project = |fields: serde_json::Value| -> Result<Overlay, String> {
        let file =
            serde_json::json!({"program": "b", "names": {}, "comments": {}, "fields": fields});
        serde_json::from_value::<ProjectFile>(file)
            .map_err(|e| e.to_string())
            .and_then(|pf| pf.to_overlay())
    };
    for (fields, says) in [
        (
            serde_json::json!({"C": {"zz": "m_a"}}),
            "fields of C key 'zz' is not an address",
        ),
        (
            serde_json::json!({"C": {"0x10": "m_a", "16": "m_b"}}),
            "fields of C keys '0x10' and '16' both name 0x10; keep one",
        ),
        (
            serde_json::json!({"C": {"0x10": "m_a three words"}}),
            "the field of C at 0x10: ",
        ),
        (
            serde_json::json!({"C": {"0x10": "two-words"}}),
            "field name 'two-words' is not an identifier",
        ),
        (
            serde_json::json!({"C": {"0x10": "field_0x10"}}),
            "field_0x10 is how an unnamed field prints",
        ),
        (
            serde_json::json!({"C": {"0x10": "m_a", "0x18": "m_a"}}),
            "m_a already names +0x10 of class C; pick another name for +0x18",
        ),
        (
            serde_json::json!({"C": {"0xffffffffffffffff": "m_a u32"}}),
            "resolves to no size at 0xffffffffffffffff",
        ),
    ] {
        let refused = project(fields.clone()).expect_err("the hostile project loaded");
        assert!(refused.contains(says), "{fields}: {refused}");
    }
    let crowded: serde_json::Map<String, serde_json::Value> = (0..257)
        .map(|k| (format!("{:#x}", k * 8), format!("m_{k}").into()))
        .collect();
    let refused = project(serde_json::json!({"C": crowded})).expect_err("257 fields");
    assert!(
        refused.contains("class C would state 257 fields"),
        "{refused}"
    );
    let classes: serde_json::Map<String, serde_json::Value> = (0..4097)
        .map(|k| (format!("C{k}"), serde_json::json!({"0x0": "m_a"})))
        .collect();
    let refused = project(classes.into()).expect_err("4097 classes");
    assert!(refused.contains("4097 classes"), "{refused}");
    assert!(project(serde_json::json!({"C": {"0x10": "m_a u32", "0x14": "m_b"}})).is_ok());
}

/// A project's stated fields show wherever the class's fields do.
///
/// That is the class's layout, its methods' text, the type and annotation
/// listings and the session's counts; another class's text stays as it
/// was, and a save writes the fields back as they were loaded.
#[test]
fn a_loaded_project_s_stated_fields_show_in_every_listing() {
    let (mut client, dir, image) = session("listed");
    let before = rows(&mut client, "class_2800");
    let other = text_of(&mut client, "0x1140");
    let bytes = std::fs::read(&image).expect("the image reads back");
    let project = dir.join("stated.json");
    let stated = serde_json::json!({
        "program": image, "sha256": identity(&bytes), "names": {}, "comments": {},
        "fields": {"class_2800": {"0x270": "m_currentPipeline u32", "0x18": "m_next"}}
    });
    std::fs::write(&project, stated.to_string()).expect("the project is writable");
    let path = project.to_string_lossy().into_owned();
    let loaded = client.text(
        "load_project",
        &serde_json::json!({"path": path}).to_string(),
    );
    assert!(
        loaded.starts_with("loaded 0 names + 0 comments + 0 types + 0 applied + 2 stated fields\n"),
        "{loaded}"
    );
    let after = rows(&mut client, "class_2800");
    let changed: Vec<&String> = after.iter().filter(|row| !before.contains(row)).collect();
    assert_eq!(
        changed,
        [
            "+0x18   u64 m_next  1/0   vfunc_1  [stated]",
            "+0x270  u32 m_currentPipeline  1/2   ctor_or_dtor, vfunc_0, vfunc_1  [stated u32; = 0xffffffff]"
        ]
    );
    assert_eq!(after.len(), before.len());
    for method in ["0x1040", "0x1080"] {
        let text = text_of(&mut client, method);
        assert!(text.contains("this->m_currentPipeline"), "{text}");
    }
    assert_eq!(text_of(&mut client, "0x1140"), other);
    let types = client.text("types", "{}");
    assert!(
        types.contains("\nclass\tclass_2800\t-\t0x18 m_next, 0x270 m_currentPipeline u32\n"),
        "{types}"
    );
    let annotations = client.text("annotations", "{}");
    assert!(
        annotations.starts_with(
            "# showing 2 of 2 annotations (0 names, 0 findings, 0 open question(s), 2 stated field(s))\n"
        ) && annotations.contains("\nclass_2800+0x18 field: m_next\nclass_2800+0x270 field: m_currentPipeline u32\n"),
        "{annotations}"
    );
    let session = read(&mut client, "borer://session").expect("answers");
    assert!(
        session
            .contains(", 0 prototypes, 2 stated fields; as last saved or loaded with a project\n"),
        "{session}"
    );
    let saved = dir.join("saved.json").to_string_lossy().into_owned();
    let said = client.text(
        "save_project",
        &serde_json::json!({"path": saved}).to_string(),
    );
    assert!(
        said.starts_with("saved 0 names + 0 comments + 0 types + 2 stated fields to "),
        "{said}"
    );
    client.finish();
    let written: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&saved).expect("the project reads back"))
            .expect("a project is JSON");
    assert_eq!(written["fields"], stated["fields"]);
    std::fs::remove_dir_all(&dir).ok();
}

/// Calls `set_type` and returns what it answered, a refusal's message
/// included, without the evidence line.
///
/// # Arguments
///
/// * `client` - The session.
/// * `arguments` - The call's arguments.
fn set_type(client: &mut Client, arguments: &serde_json::Value) -> String {
    without_evidence(&client.text("set_type", &arguments.to_string()))
        .trim_end()
        .to_owned()
}

/// One field of a class is stated by the class's name or at one of its
/// methods, and nothing else changes.
///
/// The dry run says what it keeps, the layout's other rows and another
/// class's text stay byte for byte, and the session lists the call that
/// applied it once.
#[test]
fn one_field_is_stated_by_class_or_at_a_method_and_the_rest_stays() {
    let (mut client, dir, _) = session("stated");
    let before = rows(&mut client, "class_2800");
    let other = text_of(&mut client, "0x1140");
    let by_class = serde_json::json!({
        "name": "class_2800", "fields": ["0x270:m_currentPipeline:u32"], "size": 856
    });
    assert_eq!(
        set_type(&mut client, &by_class),
        "dry-run: would state 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline u32; a class keeps no stated size. pass dry_run=false to apply."
    );
    let at_method = serde_json::json!({
        "address": "0x1040", "var": "field_0x270", "name": "m_currentPipeline", "type": "u32"
    });
    assert_eq!(
        set_type(&mut client, &at_method),
        "dry-run: would state 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline u32; class_2800::vfunc_0 (0x1040) takes its object as class_2800. pass dry_run=false to apply."
    );
    let at_constructor = serde_json::json!({
        "address": "0x1000", "var": "field_0x270", "name": "m_currentPipeline"
    });
    assert_eq!(
        set_type(&mut client, &at_constructor),
        "dry-run: would state 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline (accessed 4 byte(s) wide); class_2800::ctor_or_dtor (0x1000) is named after class_2800 and takes its object untyped, so its own text will not print the name: the class's other methods do. pass dry_run=false to apply.",
        "a constructor's text takes the object untyped"
    );
    assert_eq!(
        rows(&mut client, "class_2800"),
        before,
        "a dry run writes nothing"
    );
    let apply = |call: &serde_json::Value| {
        let mut call = call.clone();
        call["dry_run"] = false.into();
        call
    };
    assert_eq!(
        set_type(&mut client, &apply(&at_method)),
        "stated 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 field_0x270 -> m_currentPipeline u32; class_2800::vfunc_0 (0x1040) takes its object as class_2800"
    );
    assert_eq!(
        set_type(&mut client, &apply(&by_class)),
        "stated 1 field(s) of class class_2800: 6 kept, 0 changed, 0 new; a class keeps no stated size",
        "the class's name states the field the method's did"
    );
    let after = rows(&mut client, "class_2800");
    let changed: Vec<&String> = after.iter().filter(|row| !before.contains(row)).collect();
    assert_eq!(
        changed,
        [
            "+0x270  u32 m_currentPipeline  1/2   ctor_or_dtor, vfunc_0, vfunc_1  [stated u32; = 0xffffffff]"
        ]
    );
    assert_eq!(after.len(), before.len());
    for method in ["0x1040", "0x1080"] {
        let text = text_of(&mut client, method);
        assert!(
            text.contains("this->m_currentPipeline") && !text.contains("field_0x270"),
            "{text}"
        );
    }
    assert_eq!(
        text_of(&mut client, "0x1140"),
        other,
        "another class's text"
    );
    let ledger = read(&mut client, "borer://session").expect("answers");
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
    let applied: Vec<&str> = ledger
        .lines()
        .filter(|l| l.starts_with("set_type {"))
        .collect();
    assert_eq!(
        applied,
        [
            r#"set_type {"address":"0x1040","dry_run":false,"name":"m_currentPipeline","type":"u32","var":"field_0x270"}"#
        ],
        "the call that changed the overlay, once: {ledger}"
    );
}

/// A field stated without a type keeps the width the class's code uses.
///
/// A type of another size is refused on the dry run with both widths and
/// the instructions, a type of that size is taken, replacing is asked for,
/// `var` is a variable before it is a field, and a field at a function of
/// no class says how to state it by the class's name.
#[test]
fn a_field_keeps_its_width_and_a_conflicting_type_is_refused() {
    let (mut client, dir, _) = session("widths");
    let untyped = serde_json::json!({
        "name": "class_2800", "fields": ["0x270:m_currentPipeline", "0x18:m_next"], "dry_run": false
    });
    assert_eq!(
        set_type(&mut client, &untyped),
        "stated 2 field(s) of class class_2800: 4 kept, 2 changed, 0 new: +0x18 field_0x18 -> m_next (accessed 8 byte(s) wide), +0x270 field_0x270 -> m_currentPipeline (accessed 4 byte(s) wide)"
    );
    let typed = |ty: &str| serde_json::json!({"name": "class_2800", "fields": [format!("0x270:m_currentPipeline:{ty}")]});
    assert_eq!(
        set_type(&mut client, &typed("u64")),
        "field m_currentPipeline at +0x270 of class class_2800 is stated u64, 8 byte(s) wide, but the class's code accesses it 4 byte(s) wide at 0x100a (class_2800::ctor_or_dtor), 0x1040 (class_2800::vfunc_0), 0x1080 (class_2800::vfunc_1); state a type of that width, or leave the type out (0x270:m_currentPipeline) to keep the width the code uses"
    );
    assert_eq!(
        set_type(&mut client, &typed("i32")),
        "dry-run: would state 1 field(s) of class class_2800: 5 kept, 1 changed, 0 new: +0x270 m_currentPipeline -> m_currentPipeline i32. pass dry_run=false to apply.",
        "a type of the width the code uses is no conflict"
    );
    let replacing = serde_json::json!({
        "name": "class_2800", "fields": ["0x20:m_bound"], "replace": true, "dry_run": false
    });
    assert_eq!(
        set_type(&mut client, &replacing),
        "stated 1 field(s) of class class_2800: 3 kept, 1 changed, 0 new, 2 dropped: +0x20 field_0x20 -> m_bound (accessed 1 byte(s) wide), +0x18 m_next (dropped), +0x270 m_currentPipeline (dropped)"
    );
    let text = text_of(&mut client, "0x1080");
    assert!(
        text.contains("this->m_bound = 1;") && text.contains("this->field_0x270 = "),
        "{text}"
    );
    let nowhere = serde_json::json!({"address": "0x11c0", "var": "field_0x10", "name": "m_count"});
    assert_eq!(
        set_type(&mut client, &nowhere),
        "sub_11c0 belongs to no class borer knows, so a field at 0x10 has no class to be stated of; state it by its class, set_type(name=<class>, fields=[\"0x10:m_count\"]), or type the pointer it is read through (borer://layout/0x11c0,apply=<Name> plans that)"
    );
    let unnamed = serde_json::json!({"address": "0x1040", "var": "field_0x10"});
    assert_eq!(
        set_type(&mut client, &unnamed),
        "naming a field needs `name`, its new name (`type` is optional)"
    );
    let decimal = serde_json::json!({"address": "0x1040", "var": "field_16", "name": "m_count"});
    assert!(
        set_type(&mut client, &decimal).starts_with("'field_16' is no parameter or stack slot"),
        "a field is named as the text prints it, its offset in hex"
    );
    for misplaced in [
        serde_json::json!({"name": "State", "values": ["Run:1"], "replace": true}),
        serde_json::json!({
            "address": "0x1040", "var": "field_0x10", "name": "m_count",
            "fields": ["0x10:m_count"], "replace": true
        }),
    ] {
        assert_eq!(
            set_type(&mut client, &misplaced),
            "`replace` drops the fields `fields` does not restate, so it goes with `name` and `fields`"
        );
    }
    let variable = serde_json::json!({
        "address": "0x1080", "var": "a2", "name": "field_0x10", "dry_run": false
    });
    assert_eq!(
        set_type(&mut client, &variable),
        "named a2 of class_2800::vfunc_1 (0x1080) field_0x10"
    );
    let renamed = serde_json::json!({"address": "0x1080", "var": "field_0x10", "name": "pipeline"});
    assert_eq!(
        set_type(&mut client, &renamed),
        "dry-run: would name a2 of class_2800::vfunc_1 (0x1080) pipeline; decompile then renders it so. pass dry_run=false to apply.",
        "a variable an agent named so is the variable still"
    );
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

/// A stated field survives `save_project` and `load_project`, and a user
/// struct takes a stated field by offset as a class does, at the CLI as
/// over MCP.
#[test]
fn a_stated_field_is_saved_and_a_struct_merges_at_the_cli_too() {
    let (mut client, dir, _) = session("saved");
    let stated = serde_json::json!({
        "address": "0x1080", "var": "field_0x270", "name": "m_currentPipeline", "dry_run": false
    });
    set_type(&mut client, &stated);
    let project = dir.join("kept.json").to_string_lossy().into_owned();
    let path = serde_json::json!({"path": project}).to_string();
    let saved = client.text("save_project", &path);
    assert!(saved.contains(" + 1 stated fields to "), "{saved}");
    let wiped = serde_json::json!({
        "name": "class_2800", "fields": ["0x18:m_next"], "replace": true, "dry_run": false
    });
    set_type(&mut client, &wiped);
    assert!(!text_of(&mut client, "0x1040").contains("m_currentPipeline"));
    let loaded = client.text("load_project", &path);
    assert!(loaded.contains(" + 1 stated fields\n"), "{loaded}");
    assert!(text_of(&mut client, "0x1040").contains("this->m_currentPipeline"));
    let define = serde_json::json!({
        "name": "Player", "fields": ["0x18:hp:u32", "0x1c:mp:u32"], "dry_run": false
    });
    assert_eq!(
        set_type(&mut client, &define),
        "defined struct Player: 2 field(s), 0x20 byte(s)"
    );
    let merge = serde_json::json!({"name": "Player", "fields": ["0x18:health"], "dry_run": false});
    let merged = "defined struct Player: 2 field(s), 0x20 byte(s); 1 kept, 1 changed, 0 new: +0x18 hp u32 -> health u32";
    assert_eq!(set_type(&mut client, &merge), merged);
    let replace = serde_json::json!({
        "name": "Player", "fields": ["0x0:id:u64"], "replace": true, "dry_run": false
    });
    let replaced = "defined struct Player: 1 field(s), 0x8 byte(s), in place of the 2 it stated";
    assert_eq!(set_type(&mut client, &replace), replaced);
    client.finish();
    let start = dir.join("start.exe").to_string_lossy().into_owned();
    let cli_project = dir.join("cli.json").to_string_lossy().into_owned();
    let cli = |fields: &[&str]| {
        let mut args = vec![
            "--no-pdb",
            "set-type",
            &start,
            &cli_project,
            "struct",
            "Player",
        ];
        args.extend(fields);
        let out = std::process::Command::new(env!("CARGO_BIN_EXE_borer"))
            .args(&args)
            .output()
            .expect("spawn borer");
        String::from_utf8_lossy(&out.stdout).into_owned()
    };
    cli(&["0x18:hp:u32", "0x1c:mp:u32"]);
    let said = cli(&["0x18:health"]);
    assert!(
        said.starts_with(&format!("{merged}; written to ")),
        "{said}"
    );
    let said = cli(&["replace", "0x0:id:u64"]);
    assert!(
        said.starts_with(&format!("{replaced}; written to ")),
        "{said}"
    );
    std::fs::remove_dir_all(&dir).ok();
}
