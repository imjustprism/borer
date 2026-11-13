//! Project persistence round-trip tests.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer::project::{Identity, ProjectFile, identity};
use borer_engine::analysis::Overlay;
use borer_engine::analysis::stated::Field;
use borer_engine::analysis::utypes::{TypeExpr, UserType, build_enum, build_struct, parse_type};
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
    pf.save(path, borer::output::Existing::Replace).unwrap();

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
    pf.save(path.to_str().unwrap(), borer::output::Existing::Replace)
        .unwrap();
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
    let vec = build_struct("Vec", Some(0x10), &fields, &o.types, 8).unwrap();
    o.types.insert("Vec".to_owned(), vec);
    o.applied.insert(0x140003000, parse_type("Vec *").unwrap());
    let dir = std::env::temp_dir().join(format!("borer-project-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("types.json");
    ProjectFile::from_overlay("bin", None, &o)
        .save(path.to_str().unwrap(), borer::output::Existing::Replace)
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
        .save(path.to_str().unwrap(), borer::output::Existing::Replace)
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

/// A project without a hash is matched by its path's text alone, so no path
/// out of a project file is opened.
///
/// The NT spelling of the loaded file, which the disk resolves to it, is
/// another path, as the path in other case is; `.` and `..` fold as the
/// text says. Both paths were canonicalized, which opened the saved one:
/// `\??\UNC\host\share\x` authenticated to the host as the user.
#[cfg(windows)]
#[test]
fn a_project_is_matched_by_its_path_text_alone() {
    let dir = std::env::temp_dir().join(format!("borer-project-text-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let bin = dir.join("bin.exe");
    std::fs::write(&bin, b"MZ").unwrap();
    let saved = |program: &str| ProjectFile::from_overlay(program, None, &Overlay::default());
    assert!(!saved(&format!(r"\??\{}", bin.display())).is_for(&bin));
    assert!(!saved(&bin.display().to_string().to_uppercase()).is_for(&bin));
    assert!(saved(&format!(r"{}\x\.\..\bin.exe", dir.display())).is_for(&bin));
    assert!(saved(r".\a.exe").is_for(std::path::Path::new("a.exe")));
    std::fs::remove_dir_all(&dir).ok();
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
    hashed
        .save(one.to_str().unwrap(), borer::output::Existing::Replace)
        .unwrap();
    hashed
        .save(two.to_str().unwrap(), borer::output::Existing::Replace)
        .unwrap();
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
    pf.save(path.to_str().unwrap(), borer::output::Existing::Replace)
        .unwrap();
    let restored = ProjectFile::load(path.to_str().unwrap())
        .unwrap()
        .to_overlay()
        .unwrap();
    assert_eq!(restored.prototypes, o.prototypes);
    assert_eq!(restored.vars, o.vars);
    assert_eq!(restored.fingerprint(), o.fingerprint());

    let plain = dir.join("plain.json");
    ProjectFile::from_overlay("bin", None, &Overlay::default())
        .save(plain.to_str().unwrap(), borer::output::Existing::Replace)
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

/// Loads a project on a thread of its own, so a load that does not end
/// fails the test instead of hanging it.
///
/// # Arguments
///
/// * `pf` - The project.
///
/// # Returns
///
/// What the load answered, or `None` when it took over ten seconds.
fn loaded_in_time(pf: ProjectFile) -> Option<Result<Overlay, String>> {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || tx.send(pf.to_overlay()).is_ok());
    rx.recv_timeout(std::time::Duration::from_secs(10)).ok()
}

/// Returns a project of classes `C0` on, each stating `fields` fields
/// typed by `A0`, the first of `chain` typedefs that each name the next,
/// the last a `u32`.
///
/// # Arguments
///
/// * `classes` - How many classes.
/// * `fields` - Fields stated of each, four bytes apart.
/// * `chain` - Typedefs in the chain.
fn typed_through_a_chain(classes: usize, fields: u64, chain: usize) -> ProjectFile {
    let mut o = Overlay::default();
    for k in 0..chain {
        let next = if k + 1 == chain {
            TypeExpr::U32
        } else {
            TypeExpr::Named(format!("A{}", k + 1))
        };
        o.types.insert(format!("A{k}"), UserType::Alias(next));
    }
    for c in 0..classes {
        let stated = o.fields.entry(format!("C{c}")).or_default();
        for k in 0..fields {
            let ty = Some(TypeExpr::Named("A0".to_owned()));
            stated.insert(
                k * 4,
                Field {
                    name: format!("m_{k}"),
                    ty,
                },
            );
        }
    }
    ProjectFile::from_overlay("bin", None, &o)
}

/// A project file whose typedefs chain past the cap, or whose tables
/// pass their counts, is refused, and the refusal the agent reads names
/// the typedef or the count. A chain at the cap loads.
///
/// The million fields and the long chains a load took hours over are
/// held to their bounds by the engine's own tests.
#[test]
fn a_hostile_project_is_refused_by_its_counts_and_its_chains() {
    let crowded = loaded_in_time(typed_through_a_chain(1, 257, 2))
        .expect("the load answers within ten seconds")
        .expect_err("257 fields of one class loaded");
    assert!(
        crowded.contains("class C0 would state 257 fields"),
        "{crowded}"
    );
    let chained = loaded_in_time(typed_through_a_chain(1, 1, 17))
        .expect("the load answers within ten seconds")
        .expect_err("a chain of 17 typedefs loaded");
    assert!(
        chained.contains("typedef 'A0' starts a chain of 17 typedefs; 16 is the most"),
        "{chained}"
    );
    assert!(loaded_in_time(typed_through_a_chain(2, 2, 16)).is_some_and(|o| o.is_ok()));
    let applied: serde_json::Map<String, serde_json::Value> = (0..0x1_0001u64)
        .map(|k| (format!("{k:#x}"), "u32".into()))
        .collect();
    let refused =
        loaded(serde_json::json!({ "applied": applied })).expect_err("65537 applied types loaded");
    assert!(refused.contains("applies 65537 types"), "{refused}");
    let prototypes: serde_json::Map<String, serde_json::Value> = (0..0x1_0001u64)
        .map(|k| (format!("{k:#x}"), "unread".into()))
        .collect();
    let refused = loaded(serde_json::json!({ "prototypes": prototypes }))
        .expect_err("65537 prototypes loaded");
    assert!(refused.contains("65537 prototypes"), "{refused}");
    let types: serde_json::Map<String, serde_json::Value> = (0..0x1001)
        .map(|k| (format!("T{k}"), serde_json::json!({"Alias": "U8"})))
        .collect();
    let counted_first = serde_json::json!({ "types": types, "applied": {"0x10": "no type"} });
    let refused = loaded(counted_first).expect_err("4097 types loaded");
    assert!(refused.contains("states 4097 types"), "{refused}");
}

/// Loads a project file of these tables, with no names or comments
/// unless it states them.
///
/// # Arguments
///
/// * `tables` - The file's tables, as JSON.
///
/// # Returns
///
/// The overlay.
///
/// # Errors
///
/// Why the file does not parse or load.
fn loaded(tables: serde_json::Value) -> Result<Overlay, String> {
    let mut file = serde_json::json!({"program": "b", "names": {}, "comments": {}});
    if let (Some(file), serde_json::Value::Object(tables)) = (file.as_object_mut(), tables) {
        file.extend(tables);
    }
    serde_json::from_value::<ProjectFile>(file)
        .map_err(|e| e.to_string())
        .and_then(|pf| pf.to_overlay())
}

/// A project whose struct holds itself by value is refused, naming the
/// cycle.
///
/// It loaded, and an alignment of it walked each of its three fields of
/// its own type to a depth cap: `3^33` steps.
#[test]
fn a_struct_holding_itself_by_value_is_refused() {
    let field = |name: &str| serde_json::json!({"name": name, "ty": {"Named": "A"}});
    let fields = serde_json::json!({"0": field("a"), "8": field("b"), "16": field("c")});
    let types = serde_json::json!({"A": {"Struct": {"size": 24, "fields": fields}}});
    let refused = loaded(serde_json::json!({ "types": types })).expect_err("A holds itself");
    assert!(
        refused.contains("type 'A' holds itself by value (A -> A)"),
        "{refused}"
    );
}

/// A project's struct that lays out only with 4-byte pointers is refused
/// on an x64 binary, as `set_type` there refuses it.
///
/// Read with the narrowest pointer alone, a size-8 struct of `p u8 *` at 0
/// and `n u32` at 4 loaded, though here the pointer covers `n`.
#[test]
fn a_struct_laid_out_for_4_byte_pointers_is_refused_on_x64() {
    let dir = std::env::temp_dir().join(format!("borer-narrow-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let binary = dir.join("a.exe");
    std::fs::write(&binary, tiny_pe()).unwrap();
    let project = dir.join("p.json");
    let fields = serde_json::json!({
        "0": {"name": "p", "ty": {"Ptr": "U8"}},
        "4": {"name": "n", "ty": "U32"}
    });
    let types = serde_json::json!({"S": {"Struct": {"size": 8, "fields": fields}}});
    let file = serde_json::json!({"program": "", "names": {}, "comments": {}, "types": types});
    std::fs::write(&project, file.to_string()).unwrap();
    let mut client = Client::start(&binary.display().to_string());
    let asked = serde_json::json!({"path": project.display().to_string(), "force": true});
    let refused = answer(&mut client, "load_project", &asked);
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
    let refused = refused.expect_err("a struct whose pointer covers its next field loaded");
    assert!(
        refused.contains(
            "struct S: field n at 0x4 overlaps p, which ends at 0x8 with the 8-byte pointers"
        ),
        "{refused}"
    );
}

/// A project's struct of 257 fields, or enum of 257 values, is refused as
/// the file is read, naming the cap.
///
/// Both were read whole, and refused only once counted.
#[test]
fn a_type_past_its_entries_is_refused_as_the_file_is_read() {
    let fields: serde_json::Map<String, serde_json::Value> = (0..257u64)
        .map(|k| {
            let field = serde_json::json!({"name": format!("f{k}"), "ty": "U8"});
            (k.to_string(), field)
        })
        .collect();
    let values: Vec<serde_json::Value> = (0..257u64)
        .map(|k| serde_json::json!([k, format!("V{k}")]))
        .collect();
    for (ty, says) in [
        (
            serde_json::json!({"Struct": {"size": 257, "fields": fields}}),
            "the project states 257 fields of one struct; 256 is the most",
        ),
        (
            serde_json::json!({"Enum": {"size": 4, "values": values}}),
            "the project states 257 values of one enum; 256 is the most",
        ),
    ] {
        let file =
            serde_json::json!({"program": "b", "names": {}, "comments": {}, "types": {"T": ty}});
        let refused = serde_json::from_str::<ProjectFile>(&file.to_string())
            .err()
            .map(|e| e.to_string())
            .unwrap_or_default();
        assert!(refused.contains(says), "{refused}");
    }
}

/// A function a project states no variable of is left out on load, so
/// the session counts the variables as the file did.
///
/// An empty table loaded and stayed; the file counted it as one variable
/// and the session as none, so a session at the cap saved a project its
/// load refused.
#[test]
fn a_function_stating_no_variable_is_left_out_on_load() {
    let o = loaded(serde_json::json!({"vars": {"0x1000": {}}})).expect("loads");
    assert!(o.vars.is_empty(), "{} functions kept", o.vars.len());
}

/// A session is held to every count a project file is: its types, its
/// prototypes, its variables and the classes it states fields of, not
/// only its names, comments and applied types.
///
/// A session past one of them saved a project its load refused.
#[test]
fn a_session_is_held_to_every_count_a_project_is() {
    use borer_engine::analysis::project::held;
    use borer_engine::analysis::protos::{Proto, VARS_MAX};
    let proto = Proto::parse("int (void)").expect("a prototype");
    let mut types = Overlay::default();
    for k in 0..4097 {
        types
            .types
            .insert(format!("T{k}"), UserType::Alias(TypeExpr::U8));
    }
    let mut prototypes = Overlay::default();
    for k in 0..0x1_0001u64 {
        prototypes.prototypes.insert(k, proto.clone());
    }
    let mut vars = Overlay::default();
    for k in 0..=borer_engine::num::from_usize(VARS_MAX) {
        vars.vars.insert(k, std::collections::BTreeMap::new());
    }
    let mut classes = Overlay::default();
    for k in 0..4097 {
        let field = Field {
            name: "m_a".to_owned(),
            ty: None,
        };
        classes.fields.insert(format!("C{k}"), [(0, field)].into());
    }
    for (o, says) in [
        (types, "4097 types"),
        (prototypes, "65537 prototypes"),
        (vars, "65537 variables"),
        (classes, "4097 classes"),
    ] {
        let refused = held(&o).expect_err("a session past a count was held");
        assert!(refused.contains(says), "{refused}");
    }
}

/// A project whose indented text passes the bytes a project file holds is
/// saved unindented, and loads back.
///
/// 4,096 structs of 256 fields loaded from a 30 MB file, and their save was
/// refused at 84 MB of indented text, blaming names and comments the
/// project did not state.
#[test]
fn a_project_too_long_indented_is_saved_unindented() {
    let dir = std::env::temp_dir().join(format!("borer-unindented-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("p.json").display().to_string();
    let mut o = Overlay::default();
    let fields: Vec<(u64, String, TypeExpr)> = (0..256u64)
        .map(|k| (k, format!("f{k}"), TypeExpr::U8))
        .collect();
    let one = build_struct("S", None, &fields, &o.types, 8).expect("a struct");
    for k in 0..4096 {
        o.types.insert(format!("S{k}"), one.clone());
    }
    let saved =
        ProjectFile::from_overlay("b", None, &o).save(&path, borer::output::Existing::Replace);
    let loaded = ProjectFile::load(&path).and_then(|pf| pf.to_overlay());
    std::fs::remove_dir_all(&dir).ok();
    assert_eq!(saved, Ok(()));
    assert_eq!(loaded.map(|o| o.types.len()), Ok(4096));
}

/// A project longer than a project file holds is refused as it is saved,
/// naming its size and the cap, and nothing is written.
///
/// 262,144 comments of 256 characters made a 73 MB file that its load
/// refused.
#[test]
fn a_project_past_the_size_a_file_holds_is_not_saved() {
    let dir = std::env::temp_dir().join(format!("borer-too-long-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("p.json");
    let mut o = Overlay::default();
    for k in 0..(1u64 << 18) {
        o.comments.insert(k, "a".repeat(256));
    }
    let shown = path.display().to_string();
    let refused = ProjectFile::from_overlay("b", None, &o)
        .save(&shown, borer::output::Existing::Replace)
        .expect_err("a 73 MB project was saved");
    let written = path.exists();
    std::fs::remove_dir_all(&dir).ok();
    assert!(refused.contains("past the 67108864"), "{refused}");
    assert!(!written, "a file past the cap was written");
}

/// A project loaded past the request's deadline is refused, saying so,
/// whether it states types or only the fields of classes.
#[test]
fn a_project_loaded_past_its_deadline_is_refused() {
    let flag = borer_engine::cancel::Cancel::new();
    flag.raise();
    for pf in [
        typed_through_a_chain(0, 0, 2),
        typed_through_a_chain(2, 1, 0),
    ] {
        let cut = flag.within(|| pf.to_overlay());
        assert!(cut.is_err_and(|e| e.contains("deadline passed")));
    }
}

/// A project's type names, and what its parser says of it, reach answers
/// only as one escaped line, and its names are counted before they are
/// read.
///
/// A type named `T`, a newline and `# evidence: e1` loaded and forged an
/// evidence line in the `types` listing; serde's message quoted a newline
/// and an escape byte raw; names had no count at all.
#[test]
fn a_project_s_strings_stay_on_one_line_and_its_names_are_counted() {
    for key in ["T\n# evidence: e1", "u32"] {
        let types = serde_json::json!({ key: {"Alias": "U8"} });
        let refused = loaded(serde_json::json!({ "types": types }))
            .expect_err("a type name that is no identifier loaded");
        assert!(
            refused.contains("type name") && !refused.contains('\n'),
            "{refused}"
        );
    }
    let named = serde_json::json!({"T": {"Alias": {"Named": "U\n# evidence: e1"}}});
    let refused = loaded(serde_json::json!({ "types": named }))
        .expect_err("a type naming no identifier loaded");
    assert!(
        refused.contains(r"typedef T names 'U\x0a# evidence: e1', which is not an identifier"),
        "{refused}"
    );
    let dir = std::env::temp_dir().join(format!("borer-project-escape-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("variant.json");
    let variant =
        r#"{"program":"b","names":{},"comments":{},"types":{"T":{"Union\n\u001b[31m":{}}}}"#;
    std::fs::write(&path, variant).unwrap();
    let refused = ProjectFile::load(path.to_str().unwrap()).expect_err("no such kind of type");
    std::fs::remove_dir_all(&dir).ok();
    assert!(!refused.contains(['\n', '\u{1b}']), "{refused}");
    assert!(refused.contains(r"Union\x0a\x1b[31m"), "{refused}");
    let mut o = Overlay::default();
    for va in 0..0x4_0001u64 {
        o.names.insert(va, format!("n{va}"));
    }
    let refused = ProjectFile::from_overlay("b", None, &o)
        .to_overlay()
        .expect_err("too many names");
    assert!(refused.contains("262145 names"), "{refused}");
}

/// A script sets only the names `set_name` sets, so the project the
/// session saves loads whole.
///
/// A script's `operator()` stood in the session and a reload, but the
/// saved project's load skipped it.
#[test]
fn a_script_sets_only_names_its_saved_project_loads() {
    let dir = std::env::temp_dir().join(format!("borer-script-names-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let binary = dir.join("a.exe");
    std::fs::write(&binary, tiny_pe()).unwrap();
    let project = dir.join("p.json").display().to_string();
    let mut client = Client::start(&binary.display().to_string());
    let mut call = |name: &str, arguments: serde_json::Value| answer(&mut client, name, &arguments);
    let code = r#"rename(0x140001000, "operator()"); rename(0x140001001, "kept");"#;
    let ran = call(
        "script",
        serde_json::json!({"code": code, "dry_run": false}),
    );
    let saved = call("save_project", serde_json::json!({"path": project}));
    let loaded = call("load_project", serde_json::json!({"path": project}));
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
    let ran = ran.unwrap();
    assert!(
        ran.contains("names at 1 addresses") && ran.contains("1 skipped"),
        "{ran}"
    );
    assert!(saved.unwrap().starts_with("saved 1 names"));
    let loaded = loaded.unwrap();
    assert!(!loaded.contains("# skipped"), "{loaded}");
}

/// The variables of one function stated under two spellings of its address
/// refuse the file, as two keys of one address do in every other table.
///
/// Each spelling was read by itself and the two merged.
#[test]
fn a_function_s_variables_under_two_keys_refuse_the_project() {
    let vars = serde_json::json!({"0x1000": {"a1": "first"}, "4096": {"a2": "second"}});
    let refused =
        loaded(serde_json::json!({ "vars": vars })).expect_err("two keys of one function loaded");
    assert!(
        refused.contains("vars keys '0x1000' and '4096' both name 0x1000; keep one"),
        "{refused}"
    );
}

/// Saving to an unusable path refuses it before serializing, and saving a
/// project past 64 MiB names its exact unindented byte count without
/// writing a file.
#[test]
fn save_checks_path_before_serializing_and_counts_exact_overflow_bytes() {
    use borer_engine::analysis::project::Project;
    let empty_len =
        serde_json::to_string(&ProjectFile::from_overlay("", None, &Overlay::default()))
            .unwrap()
            .len();
    let program_len = 70 << 20;
    let pf = ProjectFile(Project {
        program: "a".repeat(program_len),
        ..Project::default()
    });
    for bad in std::iter::once("").chain(cfg!(windows).then_some("con")) {
        let unusable = pf
            .save(bad, borer::output::Existing::Replace)
            .expect_err("saving to an unusable path was accepted");
        assert!(
            !unusable.contains("even unindented") && unusable.contains("nothing was written"),
            "{bad}: {unusable}"
        );
    }
    let dir = std::env::temp_dir().join(format!("borer-save-exact-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let dest = dir.join("huge.json");
    let refused = pf
        .save(
            &dest.display().to_string(),
            borer::output::Existing::Replace,
        )
        .expect_err("a 70 MiB project was saved");
    let exists = dest.exists();
    std::fs::remove_dir_all(&dir).ok();
    let expected = format!(
        "the project is {} bytes even unindented, past the 67108864 a project file holds",
        empty_len + program_len
    );
    assert!(refused.contains(&expected), "{refused}");
    assert!(!exists);
}

/// Refusing a 4-byte layout on x64 keeps the session overlay and blocks CLI `set-type`.
#[test]
fn x64_layout_refusal_keeps_installed_overlay_and_refuses_cli_set_type() {
    let root = std::env::temp_dir().join(format!("borer-narrow-keep-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let (exe_path, proj_path) = (root.join("bin64.exe"), root.join("narrow.json"));
    std::fs::write(&exe_path, tiny_pe()).unwrap();
    let raw = r#"{"program":"","names":{"0x140001000":"bad_load"},"comments":{},"types":{"W":{"Struct":{"size":8,"fields":{"0":{"name":"ptr","ty":{"Ptr":"U16"}},"4":{"name":"tag","ty":"U32"}}}}}}"#;
    std::fs::write(&proj_path, raw).unwrap();
    let (bin_str, proj_str) = (
        exe_path.display().to_string(),
        proj_path.display().to_string(),
    );
    let mut client = Client::start(&bin_str);
    client.text(
        "set_name",
        r#"{"address":"0x140001000","name":"kept_fn","dry_run":false}"#,
    );
    let asked = serde_json::json!({"path": &proj_str, "force": true});
    assert!(answer(&mut client, "load_project", &asked).is_err());
    let anns = client.text("annotations", "{}");
    client.finish();
    let cli = std::process::Command::new(env!("CARGO_BIN_EXE_borer"))
        .args(["set-type", &bin_str, &proj_str, "enum", "E", "4", "A:0"])
        .output()
        .unwrap();
    std::fs::remove_dir_all(&root).ok();
    assert!(
        anns.contains("kept_fn") && !anns.contains("bad_load"),
        "{anns}"
    );
    assert!(!cli.status.success());
    let stderr = String::from_utf8_lossy(&cli.stderr);
    assert!(stderr.contains("with the 8-byte pointers"), "{stderr}");
}
