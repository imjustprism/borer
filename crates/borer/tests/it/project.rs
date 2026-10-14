//! Project persistence round-trip tests.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer::project::{Identity, ProjectFile, identity};
use borer_engine::analysis::Overlay;
use borer_engine::analysis::utypes::{build_enum, build_struct, parse_type};
use borer_engine::program::{Arch, Program};

use crate::contract::tiny_pe;
use crate::reload::Client;

/// Names and comments survive a save/load round trip along with the
/// program path and its SHA-256.
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

    let pf = ProjectFile::from_overlay("D:/some/binary.exe", Some(identity(b"abc")), &o);
    pf.save(path).unwrap();

    let loaded = ProjectFile::load(path).unwrap();
    assert_eq!(loaded.program, "D:/some/binary.exe");
    assert_eq!(loaded.sha256, Some(identity(b"abc")));
    let restored = loaded.to_overlay().unwrap();
    assert_eq!(restored.names, o.names);
    assert_eq!(restored.comments, o.comments);
}

/// An empty overlay round-trips to an empty overlay.
#[test]
fn empty_overlay_round_trip() {
    let pf = ProjectFile::from_overlay("x", None, &Overlay::default());
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
    ProjectFile::from_overlay("bin", None, &o)
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
    ProjectFile::from_overlay("bin", None, &o)
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
    let pf = ProjectFile::from_overlay(&bin.display().to_string(), None, &Overlay::default());
    assert!(pf.is_for(&bin));
    assert!(pf.is_for(&dir.join("sub").join("..").join("bin.exe")));
    assert!(!pf.is_for(&dir.join("other.exe")));
    assert!(!ProjectFile::from_overlay("con", None, &Overlay::default()).is_for(&bin));
}

/// A binary is identified by the SHA-256 of its bytes, FIPS 180-4's
/// vector for `abc`.
#[test]
fn identity_is_the_sha256_of_the_bytes() {
    assert_eq!(
        identity(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
}

/// A project with a hash belongs to the same bytes wherever they were
/// loaded from, and to no other bytes at its path.
///
/// One without a hash, as a project saved before the hash reads, is
/// judged by its path. Saving twice writes the same bytes.
#[test]
fn a_project_is_identified_by_its_binarys_bytes() {
    let at = |bytes: Vec<u8>, path: &str| {
        let mut p = Program::raw(bytes, Arch::X86_64, 0, None, Vec::new());
        p.path = path.into();
        p
    };
    let bytes = vec![0xc3u8; 64];
    let mut rebuilt = bytes.clone();
    rebuilt[10] = 0x90;
    let hashed = ProjectFile::from_overlay("a.exe", Some(identity(&bytes)), &Overlay::default());
    assert_eq!(hashed.identify(&at(bytes.clone(), "a.exe")), Identity::Same);
    assert_eq!(
        hashed.identify(&at(bytes.clone(), "copy.exe")),
        Identity::Same
    );
    assert_eq!(
        hashed.identify(&at(rebuilt.clone(), "a.exe")),
        Identity::Other
    );
    let by_path = ProjectFile::from_overlay("a.exe", None, &Overlay::default());
    assert_eq!(by_path.identify(&at(rebuilt, "a.exe")), Identity::PathOnly);
    assert_eq!(
        by_path.identify(&at(bytes, "copy.exe")),
        Identity::OtherPath
    );
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (one, two) = (dir.join("one.json"), dir.join("two.json"));
    hashed.save(one.to_str().unwrap()).unwrap();
    hashed.save(two.to_str().unwrap()).unwrap();
    assert_eq!(std::fs::read(one).unwrap(), std::fs::read(two).unwrap());
}

/// Calls a tool over the session.
///
/// # Arguments
///
/// * `client` - The session.
/// * `name` - The tool.
/// * `arguments` - Its arguments.
///
/// # Returns
///
/// The text the tool answered.
///
/// # Errors
///
/// The error's message, when the tool refuses.
fn answer(
    client: &mut Client,
    name: &str,
    arguments: &serde_json::Value,
) -> Result<String, String> {
    let params = serde_json::json!({ "name": name, "arguments": arguments }).to_string();
    let line = client.call("tools/call", &params);
    let reply: serde_json::Value = serde_json::from_str(&line).unwrap_or_default();
    match reply["result"]["content"][0]["text"].as_str() {
        Some(text) if reply["result"]["isError"] != true => Ok(text.to_owned()),
        Some(text) => Err(text.to_owned()),
        None => Err(reply["error"]["message"]
            .as_str()
            .unwrap_or(&line)
            .to_owned()),
    }
}

/// Over the server, projects are keyed by hash and the ledger pages.
///
/// A project loads into a copy of its binary at another path, a rebuilt
/// binary at the same path refuses it with the carry hint until forced, a
/// project saved before the hash loads by its path and says so, and
/// `annotations` pages with `# showing N of M`. A rebuild at the same path
/// took the old names silently while the path was the identity, and
/// `annotations` listed every entry with no cap.
#[test]
fn the_server_keys_projects_by_hash_and_pages_the_ledger() {
    let dir = std::env::temp_dir().join(format!("borer-project-e2e-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (original, copy) = (dir.join("a.exe"), dir.join("copy.exe"));
    let pe = tiny_pe();
    let mut rebuild = pe.clone();
    rebuild[0x201] = 0x90;
    std::fs::write(&original, &pe).unwrap();
    std::fs::write(&copy, &pe).unwrap();
    let project = dir.join("p.json").display().to_string();
    let path = |p: &std::path::Path| p.display().to_string();
    let mut client = Client::start(&path(&original));
    let mut call = |name: &str, arguments: serde_json::Value| answer(&mut client, name, &arguments);
    for (va, name) in [("0x140001000", "kept"), ("0x140001001", "second")] {
        let args = serde_json::json!({"address": va, "name": name, "dry_run": false});
        call("set_name", args).unwrap();
    }
    let guess =
        serde_json::json!({"address": "0x140001000", "comment": "? a guess", "dry_run": false});
    call("set_comment", guess).unwrap();
    let page = call("annotations", serde_json::json!({"limit": 1})).unwrap();
    assert!(
        page.starts_with(
            "# showing 1 of 3 annotations (2 names, 0 findings, 1 open question(s))\n"
        ),
        "{page}"
    );
    assert!(
        page.contains("0x140001000  name: kept\n") && !page.contains("second"),
        "{page}"
    );
    let next = call("annotations", serde_json::json!({"offset": 2, "limit": 1})).unwrap();
    assert!(next.contains("open:  a guess"), "{next}");
    let only = call(
        "annotations",
        serde_json::json!({"count_only": true, "filter": "SECOND"}),
    )
    .unwrap();
    assert_eq!(
        crate::without_evidence(&only),
        "# 1 annotations (2 names, 0 findings, 1 open question(s))\n"
    );
    let saved = call("save_project", serde_json::json!({"path": project})).unwrap();
    assert!(saved.starts_with("saved 2 names"), "{saved}");
    assert!(
        std::fs::read_to_string(&project)
            .unwrap()
            .contains(&identity(&pe))
    );

    call("load_binary", serde_json::json!({"path": path(&copy)})).unwrap();
    let moved = call("load_project", serde_json::json!({"path": project})).unwrap();
    assert!(moved.starts_with("loaded 2 names + 1 comments"), "{moved}");
    let lines: Vec<&str> = moved.lines().collect();
    assert_eq!(lines.len(), 2, "a copy loads without a note: {moved}");
    assert!(lines[1].starts_with("# evidence: "), "{moved}");

    std::fs::write(&original, &rebuild).unwrap();
    call("load_binary", serde_json::json!({"path": path(&original)})).unwrap();
    let refused = call("load_project", serde_json::json!({"path": project})).unwrap_err();
    assert!(
        refused.starts_with("the project was saved for another build (sha-256 "),
        "{refused}"
    );
    let carry = format!(
        "then borer://carry/{} carries",
        path(&original).replace('\\', "/")
    );
    assert!(refused.contains(&carry), "{refused}");
    let ledger = call("annotations", serde_json::json!({})).unwrap();
    assert!(
        ledger.starts_with("# showing 0 of 0 annotations"),
        "nothing was loaded: {ledger}"
    );
    let forced = call(
        "load_project",
        serde_json::json!({"path": project, "force": true}),
    )
    .unwrap();
    assert!(forced.contains("# forced: "), "{forced}");

    let old = dir.join("old.json").display().to_string();
    let legacy = serde_json::json!({
        "program": path(&original),
        "names": {"0x140001000": "legacy"},
        "comments": {}
    });
    std::fs::write(&old, legacy.to_string()).unwrap();
    let by_path = call("load_project", serde_json::json!({"path": old})).unwrap();
    assert!(by_path.starts_with("loaded 1 names"), "{by_path}");
    assert!(
        by_path.contains("# the project names its binary by path alone"),
        "{by_path}"
    );
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

/// Stated prototypes and variables survive a save/load round trip.
///
/// They are keyed by function and by the variable's word-free name; a
/// project that states none writes neither table, and one whose prototype
/// does not parse is refused with the address named.
#[test]
fn prototypes_and_variables_round_trip_through_json() {
    use borer_engine::analysis::protos::{Proto, Var, VarKey};
    let mut o = Overlay::default();
    o.prototypes.insert(
        0x140001000,
        Proto::parse("int __fastcall f(Player *p, uint32_t n)").unwrap(),
    );
    let mut vars = std::collections::BTreeMap::new();
    vars.insert(VarKey::Slot(-0x58), Var::parse("wchar_t *path").unwrap());
    vars.insert(VarKey::Slot(0x30), Var::parse("spill").unwrap());
    vars.insert(VarKey::Param(1), Var::parse("count").unwrap());
    o.vars.insert(0x140001000, vars);
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("protos.json");
    let pf = ProjectFile::from_overlay("bin", None, &o);
    assert_eq!(
        pf.prototypes.get("0x140001000").map(String::as_str),
        Some("int __fastcall (Player *p, uint32_t n)")
    );
    assert_eq!(
        pf.vars
            .get("0x140001000")
            .and_then(|v| v.get("local_58"))
            .map(String::as_str),
        Some("wchar_t *path")
    );
    pf.save(path.to_str().unwrap()).unwrap();
    let restored = ProjectFile::load(path.to_str().unwrap())
        .unwrap()
        .to_overlay()
        .unwrap();
    assert_eq!(restored.prototypes, o.prototypes);
    assert_eq!(restored.vars, o.vars);
    assert_eq!(restored.fingerprint(), o.fingerprint());

    let plain = dir.join("plain.json");
    ProjectFile::from_overlay("bin", None, &Overlay::default())
        .save(plain.to_str().unwrap())
        .unwrap();
    let text = std::fs::read_to_string(&plain).unwrap();
    assert!(
        !text.contains("prototypes") && !text.contains("vars"),
        "{text}"
    );

    let bad = dir.join("bad-proto.json");
    std::fs::write(
        &bad,
        r#"{"program":"bin","names":{},"comments":{},"prototypes":{"0x401000":"int f"}}"#,
    )
    .unwrap();
    let err = ProjectFile::load(bad.to_str().unwrap())
        .unwrap()
        .to_overlay()
        .unwrap_err();
    assert!(
        err.contains("0x401000") && err.contains("parameter list"),
        "{err}"
    );
}
