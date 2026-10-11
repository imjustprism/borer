//! Project persistence round-trip tests.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer::project::ProjectFile;
use borer_engine::analysis::Overlay;
use borer_engine::analysis::utypes::{build_enum, build_struct, parse_type};

/// Names and comments survive a save/load round trip along with the program path.
#[test]
fn overlay_round_trip_through_json() {
    let mut o = Overlay::default();
    o.names.insert(0x140001000, "main".to_owned());
    o.names.insert(0x140002000, "decrypt_strings".to_owned());
    o.comments
        .insert(0x140001024, "xor loop over .rdata".to_owned());

    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("t.json");
    let path = path.to_str().unwrap();

    let pf = ProjectFile::from_overlay("D:/some/binary.exe", &o);
    pf.save(path).unwrap();

    let loaded = ProjectFile::load(path).unwrap();
    assert_eq!(loaded.program, "D:/some/binary.exe");
    let restored = loaded.to_overlay().unwrap();
    assert_eq!(restored.names, o.names);
    assert_eq!(restored.comments, o.comments);
}

/// An empty overlay round-trips to an empty overlay.
#[test]
fn empty_overlay_round_trip() {
    let pf = ProjectFile::from_overlay("x", &Overlay::default());
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("empty.json");
    pf.save(path.to_str().unwrap()).unwrap();
    let loaded = ProjectFile::load(path.to_str().unwrap()).unwrap();
    assert!(loaded.to_overlay().unwrap().names.is_empty());
}

/// User-defined types and their applications survive a save/load round
/// trip, applications by their spelling, and a project older than user
/// types loads as having none.
#[test]
fn types_round_trip_through_json() {
    let fields = vec![
        (0x0, "x".to_owned(), parse_type("f32").unwrap()),
        (0x8, "target".to_owned(), parse_type("Vec *").unwrap()),
    ];
    let mut o = Overlay::default();
    o.types.insert(
        "Vec".to_owned(),
        build_struct("Vec", Some(0x10), &fields, &o.types, 8).unwrap(),
    );
    o.applied.insert(0x140003000, parse_type("Vec *").unwrap());
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("types.json");
    ProjectFile::from_overlay("bin", &o)
        .save(path.to_str().unwrap())
        .unwrap();
    let loaded = ProjectFile::load(path.to_str().unwrap()).unwrap();
    let restored = loaded.to_overlay().unwrap();
    assert_eq!(restored.types, o.types);
    assert_eq!(restored.applied, o.applied);

    let old = r#"{"program":"bin","names":{},"comments":{}}"#;
    let path = dir.join("old.json");
    std::fs::write(&path, old).unwrap();
    let loaded = ProjectFile::load(path.to_str().unwrap()).unwrap();
    assert!(loaded.to_overlay().unwrap().types.is_empty());
}

/// An enum survives a save/load round trip with its applications, which
/// spell it by name like any named type.
#[test]
fn an_enum_round_trips_through_json() {
    let mut o = Overlay::default();
    o.types.insert(
        "State".to_owned(),
        build_enum(
            "State",
            4,
            &[(1u64, "Run".to_owned()), (0u64, "Idle".to_owned())],
        )
        .unwrap(),
    );
    o.applied.insert(0x140003020, parse_type("State").unwrap());
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("enum.json");
    ProjectFile::from_overlay("bin", &o)
        .save(path.to_str().unwrap())
        .unwrap();
    let loaded = ProjectFile::load(path.to_str().unwrap()).unwrap();
    let restored = loaded.to_overlay().unwrap();
    assert_eq!(restored.types, o.types);
    assert_eq!(restored.applied, o.applied);
}

/// A hand-edited project that applies a type the language does not spell,
/// one no definition states, or an enum a build would have refused, is
/// refused with a message naming it.
#[test]
fn a_hostile_project_refuses_its_types() {
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for (name, json, names_garbage) in [
        (
            "garbage.json",
            r#"{"program":"b","names":{},"comments":{},"applied":{"0x3000":"three of them"}}"#,
            "applied at 0x3000",
        ),
        (
            "unknown.json",
            r#"{"program":"b","names":{},"comments":{},"applied":{"0x3000":"Nope *"}}"#,
            "0x3000",
        ),
        (
            "dupenum.json",
            r#"{"program":"b","names":{},"comments":{},"types":{"State":{"Enum":{"size":4,"values":[[0,"A"],[0,"B"]]}}}}"#,
            "names value 0 twice",
        ),
    ] {
        let path = dir.join(name);
        std::fs::write(&path, json).unwrap();
        let loaded = ProjectFile::load(path.to_str().unwrap()).unwrap();
        let err = loaded.to_overlay().expect_err("the hostile project loaded");
        assert!(err.contains(names_garbage), "{name}: {err}");
    }
}

/// Address keys read as an address argument does: `0x`-hex, or plain
/// digits as decimal. A key that is not an address, or two keys naming one
/// address, refuse the file with a message naming the keys.
///
/// An unparsable key once loaded as `0x0` and a decimal one as hex, and the
/// load reported every entry of the file as loaded.
#[test]
fn a_project_refuses_keys_that_are_not_addresses() {
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let load = |name: &str, json: &str| {
        let path = dir.join(name);
        std::fs::write(&path, json).unwrap();
        ProjectFile::load(path.to_str().unwrap())
            .unwrap()
            .to_overlay()
    };
    let decimal = load(
        "decimal.json",
        r#"{"program":"b","names":{"5368713316":"dec","0x140001070":"hex"},"comments":{}}"#,
    )
    .unwrap();
    assert_eq!(
        decimal.names.into_iter().collect::<Vec<_>>(),
        vec![
            (0x1_4000_1064, "dec".to_owned()),
            (0x1_4000_1070, "hex".to_owned())
        ]
    );
    let bad = load(
        "badkey.json",
        r#"{"program":"b","names":{"notanaddr":"n1","0xZZZ":"n2","":"n3","0x10":"ok"},"comments":{}}"#,
    )
    .expect_err("unparsable keys loaded");
    assert!(
        bad.contains("names keys '', '0xZZZ', 'notanaddr' are not an address"),
        "{bad}"
    );
    let comment = load(
        "badcomment.json",
        r#"{"program":"b","names":{},"comments":{"here":"c"}}"#,
    )
    .expect_err("an unparsable comment key loaded");
    assert!(
        comment.contains("comments key 'here' is not an address"),
        "{comment}"
    );
    let applied = load(
        "badapplied.json",
        r#"{"program":"b","names":{},"comments":{},"applied":{"g_x":"u32"}}"#,
    )
    .expect_err("an unparsable applied key loaded");
    assert!(applied.contains("applied key 'g_x'"), "{applied}");
    let twice = load(
        "twice.json",
        r#"{"program":"b","names":{"0x140001064":"hex","5368713316":"dec"},"comments":{}}"#,
    )
    .expect_err("two keys naming one address loaded");
    assert!(twice.contains("both name 0x140001064"), "{twice}");
}

/// A project is for the binary at the path it records, however that path
/// is spelled, and for no other.
#[test]
fn a_project_is_for_the_file_it_was_saved_for() {
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(dir.join("sub")).unwrap();
    let bin = dir.join("bin.exe");
    std::fs::write(&bin, b"MZ").unwrap();
    let pf = ProjectFile::from_overlay(&bin.display().to_string(), &Overlay::default());
    assert!(pf.is_for(&bin));
    assert!(pf.is_for(&dir.join("sub").join("..").join("bin.exe")));
    assert!(!pf.is_for(&dir.join("other.exe")));
    assert!(!ProjectFile::from_overlay("con", &Overlay::default()).is_for(&bin));
}
