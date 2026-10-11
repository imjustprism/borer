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
