use crate::testing::raw_server;

/// A rename and a comment each let go of the text read under the names
/// before them: the old text is not kept beside the new one, and the
/// new one carries the name.
///
/// # Panics
///
/// When a text read under replaced names stays held, or the text read
/// after the rename lacks the new name.
#[test]
fn a_rename_lets_go_of_the_text_read_under_the_old_names() {
    use crate::params::DecompileParams;
    use crate::params::SetCommentParams;
    use crate::params::SetNameParams;
    use rmcp::handler::server::wrapper::Parameters;
    let server = raw_server();
    let decompile = || {
        server
            .decompile(Parameters(DecompileParams {
                address: "0x1000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: Some(u32::MAX),
            }))
            .expect("decompiles")
    };
    let held = || {
        server
            .analysis(borer_engine::program::Feature::Decompile)
            .expect("analyzed")
            .derived
            .held("plain_text")
    };
    assert!(!decompile().contains("renamed"));
    assert_eq!(held(), 1);
    server
        .set_name(Parameters(SetNameParams {
            address: Some("0x1000".to_owned()),
            name: Some("renamed".to_owned()),
            names: None,
            force: None,
            dry_run: Some(false),
        }))
        .expect("renames");
    assert_eq!(held(), 0, "the text under the old name is let go");
    assert!(decompile().contains("renamed"));
    assert_eq!(held(), 1);
    server
        .set_comment(Parameters(SetCommentParams {
            address: "0x1000".to_owned(),
            comment: "seen".to_owned(),
            dry_run: Some(false),
        }))
        .expect("comments");
    assert_eq!(held(), 0, "the text without the comment is let go");
}

/// A rename of an address a text did not read keeps the text, filed
/// under the new names, so the next decompile builds nothing.
///
/// # Panics
///
/// When the text is let go, or the decompile after the rename builds
/// a result or answers other bytes.
#[test]
fn a_rename_keeps_the_texts_that_did_not_read_the_name() {
    use crate::params::DecompileParams;
    use crate::params::SetNameParams;
    use rmcp::handler::server::wrapper::Parameters;
    let server = raw_server();
    let decompile = || {
        server
            .decompile(Parameters(DecompileParams {
                address: "0x1000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: Some(u32::MAX),
            }))
            .expect("decompiles")
    };
    let derived = || {
        let a = server
            .analysis(borer_engine::program::Feature::Decompile)
            .expect("analyzed");
        (a.derived.held("plain_text"), a.derived.builds())
    };
    let text = decompile();
    assert_eq!(derived().0, 1);
    server
        .set_name(Parameters(SetNameParams {
            address: Some("0x1080".to_owned()),
            name: Some("elsewhere".to_owned()),
            names: None,
            force: None,
            dry_run: Some(false),
        }))
        .expect("renames");
    let (held, built) = derived();
    assert_eq!(held, 1, "the text is carried over");
    assert_eq!(decompile(), text);
    assert_eq!(derived(), (1, built), "the decompile built nothing");
}

/// `set_name` refuses a name that is not an identifier and one another
/// address holds unless forced, and `names` renames many in one call,
/// checking all before applying any.
///
/// # Panics
///
/// When a bad or taken name is accepted, or the batch applies in part.
#[test]
fn set_name_refuses_bad_and_taken_names_and_renames_in_batches() {
    use crate::params::SetNameParams;
    use rmcp::handler::server::wrapper::Parameters;
    let server = raw_server();
    let set = |address: Option<&str>, name: Option<&str>, names: Option<&[&str]>, force| {
        server.set_name(Parameters(SetNameParams {
            address: address.map(str::to_owned),
            name: name.map(str::to_owned),
            names: names.map(|n| n.iter().map(|s| (*s).to_owned()).collect()),
            force,
            dry_run: Some(false),
        }))
    };
    let spaced = set(Some("0x1000"), Some("foo bar"), None, None).expect_err("a space");
    assert!(spaced.message.contains("holds ' '"), "{}", spaced.message);
    let digit = set(Some("0x1000"), Some("1st"), None, None).expect_err("a digit");
    assert!(
        digit.message.contains("opens with a digit"),
        "{}",
        digit.message
    );
    set(Some("0x1000"), Some("Foo::bar<int>"), None, None).expect("a C++ name");
    set(Some("0x1010"), Some("main"), None, None).expect("a free name");
    let taken = set(Some("0x1020"), Some("main"), None, None).expect_err("taken");
    assert!(
        taken.message.contains("0x1010") && taken.message.ends_with("force=true to take it"),
        "{}",
        taken.message
    );
    set(Some("0x1020"), Some("main"), None, Some(true)).expect("forced");
    assert!(set(None, None, None, None).is_err(), "nothing asked");
    let half = set(None, None, Some(&["0x1030=one", "0x1040=two words"]), None);
    assert!(half.is_err(), "one bad name refuses the batch");
    let bad_pair =
        set(None, None, Some(&["0x1030=one", "0x1040=one"]), None).expect_err("one name twice");
    assert!(
        bad_pair.message.starts_with("0x1040=one: 'one' ") && bad_pair.message.contains("0x1030"),
        "{}",
        bad_pair.message
    );
    assert!(
        !crate::state::read_lock(&server.overlay)
            .names
            .values()
            .any(|n| n == "one"),
        "a refused batch applies nothing"
    );
    let both = set(None, None, Some(&["0x1030=one", "0x1040 = two"]), None).expect("renames");
    assert_eq!(both.lines().count(), 2, "{both}");
    let names = &crate::state::read_lock(&server.overlay).names;
    assert_eq!(names.get(&0x1030).map(String::as_str), Some("one"));
    assert_eq!(names.get(&0x1040).map(String::as_str), Some("two"));
}

/// A name that reads as a number is noted when set and reaches its
/// function afterwards.
///
/// `0x` text stays the address, and bare digits naming nothing are
/// decimal, with the hex spelling suggested when that is the function
/// meant.
///
/// # Panics
///
/// When the note is missing, the name does not resolve, or the decimal
/// reading is not explained.
#[test]
fn a_name_that_reads_as_a_number_is_noted_and_reachable() {
    use crate::params::FunctionDetailParams;
    use crate::params::SetNameParams;
    use rmcp::handler::server::wrapper::Parameters;
    let server = raw_server();
    let set = server
        .set_name(Parameters(SetNameParams {
            address: Some("0x1000".to_owned()),
            name: Some("cafe".to_owned()),
            names: None,
            force: None,
            dry_run: Some(false),
        }))
        .expect("renames");
    assert!(set.contains("also reads as the number 0xcafe"), "{set}");
    let function = |address: &str| {
        server.function(Parameters(FunctionDetailParams {
            address: address.to_owned(),
            offset: None,
        }))
    };
    let by_name = function("cafe").expect("the name resolves");
    assert!(by_name.contains("cafe"), "{by_name}");
    assert!(function("0xcafe").is_err(), "0x text is the address");
    let decimal = function("1000").expect_err("decimal 1000 is 0x3e8");
    assert!(
        decimal
            .message
            .contains("bare digits are decimal, write 0x1000"),
        "{decimal:?}"
    );
}

/// `set_type` dry-runs by default, defines a struct and applies it at a
/// data global, and `types` lists both.
///
/// A type the language does not spell, a field naming nothing defined
/// and a global inside a function are refused with a message naming
/// the offender.
///
/// # Panics
///
/// When the dry run writes, the listing misses what was stated, or a
/// refusal accepts.
#[test]
fn set_type_defines_applies_and_refuses() {
    use crate::params::SetTypeParams;
    use crate::params::TypesParams;
    use borer_engine::program::{Arch, Program, Section};
    use rmcp::handler::server::wrapper::Parameters;
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
    let program = Program::raw(
        vec![0xcc; 0x200],
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![text, data],
    );
    let server = crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    };
    let fields = || vec!["0x18:hp:u32".to_owned(), "0x1c:mp:u32".to_owned()];
    let out = server
        .set_type(Parameters(SetTypeParams {
            name: Some("Player".to_owned()),
            fields: Some(fields()),
            values: None,
            size: None,
            address: Some("0x2000".to_owned()),
            r#type: Some("Player *".to_owned()),
            dry_run: None,
            ..SetTypeParams::default()
        }))
        .expect("dry-runs");
    assert!(
        out.starts_with("dry-run: would define struct Player"),
        "{out}"
    );
    let listed = server
        .types(Parameters(TypesParams {
            filter: None,
            offset: None,
            limit: None,
            count_only: Some(true),
        }))
        .expect("lists");
    assert!(listed.contains("0 rows (0 type(s), 0 applied)"), "{listed}");
    let out = server
        .set_type(Parameters(SetTypeParams {
            name: Some("Player".to_owned()),
            fields: Some(fields()),
            values: None,
            size: None,
            address: Some("0x2000".to_owned()),
            r#type: Some("Player *".to_owned()),
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect("defines and applies");
    assert!(
        out.contains("defined struct Player: 2 field(s), 0x20 byte(s)"),
        "{out}"
    );
    assert!(out.contains("applied Player * at 0x2000"), "{out}");
    let listed = server
        .types(Parameters(TypesParams {
            filter: Some("player".to_owned()),
            offset: None,
            limit: None,
            count_only: None,
        }))
        .expect("lists");
    assert!(
        listed.contains("struct\tPlayer\t0x20\t0x18 hp u32, 0x1c mp u32"),
        "{listed}"
    );
    assert!(listed.contains("applied\t0x2000\t-\tPlayer *"), "{listed}");
    let bad = server
        .set_type(Parameters(SetTypeParams {
            name: None,
            fields: None,
            values: None,
            size: None,
            address: Some("0x2000".to_owned()),
            r#type: Some("three of them".to_owned()),
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect_err("garbage refused");
    assert!(bad.message.contains("'three of them'"), "{}", bad.message);
    let mut unknown = fields();
    unknown.push("0x20:next:Missing *".to_owned());
    let bad = server
        .set_type(Parameters(SetTypeParams {
            name: Some("Player".to_owned()),
            fields: Some(unknown),
            values: None,
            size: None,
            address: None,
            r#type: None,
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect_err("unknown name refused");
    assert!(
        bad.message.contains("resolves to no size"),
        "{}",
        bad.message
    );
    let bad = server
        .set_type(Parameters(SetTypeParams {
            name: None,
            fields: None,
            values: None,
            size: None,
            address: Some("0x1000".to_owned()),
            r#type: Some("u32".to_owned()),
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect_err("code refused");
    assert!(
        bad.message.contains("types apply to data globals"),
        "{}",
        bad.message
    );
}

/// A server holding one x64 function that reads and writes three fields
/// through `rcx`, at 0x401000.
fn record_server() -> crate::BorerServer {
    use borer_engine::program::{Arch, Program, Section};
    let mut bytes = vec![0xccu8; 0x1000];
    bytes[..12].copy_from_slice(&[
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0x48, 0x03, 0x41, 0x18, // ASM: add rax, [rcx+0x18]
        0xc6, 0x41, 0x20, 0x01, // ASM: mov byte [rcx+0x20], 1
        0xc3, // ASM: ret
    ]);
    let text = Section::mapped(".text", 0x401_000, 0, 0x1000, false, true);
    let program = Program::raw(bytes, Arch::X86_64, 0x400_000, Some(0x401_000), vec![text]);
    crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    }
}

/// `borer://layout/...,apply=Name` plans a struct and the parameter typed
/// with it, and applies nothing.
///
/// The read names the struct, the prototype and the `set_type` calls
/// that state them, and writes nothing whatever `dry_run` it is told;
/// those calls sent as they are state what the plan holds, and the
/// re-decompiled function reads `a1->f_10`; a script cannot apply
/// through `query`.
///
/// # Panics
///
/// When a read writes, the calls state another struct than the plan's,
/// the applied text misses a field, or a refusal accepts.
#[test]
fn a_layout_applies_as_a_struct_on_request() {
    use crate::params::ClassLayoutParams;
    use crate::params::DecompileParams;
    use crate::params::ScriptParams;
    use crate::params::TypesParams;
    use rmcp::handler::server::wrapper::Parameters;
    let server = record_server();
    let types = || {
        server
            .types(Parameters(TypesParams {
                filter: None,
                offset: None,
                limit: None,
                count_only: Some(true),
            }))
            .expect("lists")
    };
    let before = server.overlay_plain();
    let dry = server
        .resource_text("borer://layout/0x401000,rcx,apply=Rec")
        .expect("a plan");
    assert_eq!(
        dry,
        "plan: struct Rec and 1 prototype(s), nothing applied by a read; send the set_type calls below and decompile names the fields:\nstruct Rec (0x21 bytes): 0x10 f_10 u32, 0x18 f_18 u64, 0x20 f_20 u8\nprototype sub_401000 (0x401000): uint64_t (Rec *)\nset_type {\"dry_run\":false,\"fields\":[\"0x10:f_10:u32\",\"0x18:f_18:u64\",\"0x20:f_20:u8\"],\"name\":\"Rec\",\"size\":33}\nset_type {\"address\":\"0x401000\",\"dry_run\":false,\"type\":\"uint64_t (Rec *)\"}\n"
    );
    assert!(types().starts_with("# 0 rows"), "{}", types());
    let scripted = server
        .script(Parameters(ScriptParams {
            code: "print(query(\"borer://layout/0x401000,apply=Rec,dry_run=false\"));".to_owned(),
            dry_run: None,
        }))
        .expect("a script answers");
    assert!(
        scripted.contains("applies nothing through query"),
        "{scripted}"
    );
    assert!(types().starts_with("# 0 rows"), "{}", types());
    let done = server
        .resource_text("borer://layout/0x401000,apply=Rec,dry_run=false")
        .expect("plans");
    assert_eq!(done, dry);
    assert_eq!(server.overlay_plain().fingerprint(), before.fingerprint());
    let program = server.loaded().expect("a program is loaded");
    let analysis = server.ensure_analysis().expect("analyzes");
    let mut planned = before.clone();
    borer_engine::analysis::apply::from_pointer(&program, &analysis, &before, "0x401000", "Rec")
        .expect("plans")
        .apply(&mut planned);
    for call in done.lines().filter_map(|l| l.strip_prefix("set_type ")) {
        let params = serde_json::from_str(call).expect("the call's arguments");
        server.set_type(Parameters(params)).expect("applies");
    }
    let stated = server.overlay_plain();
    assert_eq!(
        (&stated.types, &stated.prototypes),
        (&planned.types, &planned.prototypes),
        "the calls state what the read used to apply"
    );
    assert!(
        types().starts_with("# 2 rows (1 type(s), 0 applied)"),
        "{}",
        types()
    );
    let text = server
        .decompile(Parameters(DecompileParams {
            address: "0x401000".to_owned(),
            detail: None,
            filter: None,
            offset: None,
            limit: None,
        }))
        .expect("decompiles");
    assert!(text.contains("a1->f_10"), "{text}");
    assert!(text.contains("a1->f_20 = 1;"), "{text}");
    let bad = server
        .resource_text("borer://layout/0x401003,apply=Rec")
        .expect_err("mid-function");
    assert!(
        bad.message.contains("carries no parameter"),
        "{}",
        bad.message
    );
    let no_class = server
        .class_layout(Parameters(ClassLayoutParams {
            class: "Nope".to_owned(),
            apply: Some("N".to_owned()),
            dry_run: None,
        }))
        .expect_err("no such class");
    assert!(
        no_class.message.contains("no function belongs"),
        "{}",
        no_class.message
    );
}

/// `set_type` with `type` alone reads C declarations by the binary's ABI.
///
/// The dry run shows the offsets and writes nothing, the applied struct
/// reads with `read type=`, and a failing offset assertion is refused
/// with the field named.
///
/// # Panics
///
/// When a layout differs, the dry run writes, or a refusal accepts.
#[test]
fn set_type_reads_c_declarations() {
    use crate::params::ReadParams;
    use crate::params::SetTypeParams;
    use crate::params::TypesParams;
    use borer_engine::program::{Arch, Program, Section};
    use rmcp::handler::server::wrapper::Parameters;
    let decl = |server: &crate::BorerServer, text: &str, dry_run: Option<bool>| {
        server.set_type(Parameters(SetTypeParams {
            name: None,
            fields: None,
            values: None,
            size: None,
            address: None,
            r#type: Some(text.to_owned()),
            dry_run,
            ..SetTypeParams::default()
        }))
    };
    let server_for = |arch: Arch| {
        let mut bytes = vec![0u8; 0x200];
        bytes[0x100] = b'A';
        bytes[0x104..0x108].copy_from_slice(&7u32.to_le_bytes());
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let program = Program::raw(bytes, arch, 0, None, vec![data]);
        crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..crate::BorerServer::default()
        }
    };
    let text = "#pragma pack(push, 8)\nstruct S {\n  char c;\n  int n;   // @0x4\n  char *p;\n};\n#pragma pack(pop)\nstatic_assert(sizeof(S) == 16);";
    let x64 = server_for(Arch::X86_64);
    let dry = decl(&x64, text, None).expect("dry-runs");
    assert_eq!(
        dry,
        "dry-run: would define 1 type(s) from C, laid out for x64 Windows:\nstruct S (0x10 bytes, align 8): 0x0 c char, 0x4 n i32, 0x8 p char *\npass dry_run=false to apply.\n"
    );
    let listed = x64
        .types(Parameters(TypesParams {
            filter: None,
            offset: None,
            limit: None,
            count_only: Some(true),
        }))
        .expect("lists");
    assert!(listed.contains("0 rows (0 type(s)"), "{listed}");
    let done = decl(&x64, text, Some(false)).expect("defines");
    assert!(done.starts_with("defined 1 type(s) from C"), "{done}");
    let read = x64
        .read(Parameters(ReadParams {
            address: "0x2000".to_owned(),
            kind: None,
            r#type: Some("S".to_owned()),
            count: None,
        }))
        .expect("reads");
    assert!(read.contains("0x2000       c char   'A'\n"), "{read}");
    assert!(read.contains("0x2004       n i32    7\n"), "{read}");
    let x86 = server_for(Arch::X86);
    let narrow = decl(&x86, "struct S { char c; int n; char *p; };", None).expect("x86");
    assert!(
        narrow.contains("laid out for x86 Windows:\nstruct S (0xc bytes, align 4)"),
        "{narrow}"
    );
    let wrong = decl(
        &x64,
        "struct T {\n  char c;\n  int n;   // @0x2\n};",
        Some(false),
    )
    .expect_err("a failing assertion");
    assert!(
        wrong
            .message
            .contains("line 3: field n of struct T is at 0x4 under x64 Windows layout, not 0x2"),
        "{}",
        wrong.message
    );
}

/// `read` with `type` lays a defined struct over the bytes: `count`
/// records, each field a row with a `char` array quoted; a kind beside
/// a type, and a file offset, are refused.
///
/// # Panics
///
/// When a row is missing or a refusal accepts.
#[test]
fn read_lays_a_user_type_over_the_bytes() {
    use crate::params::ReadKind;
    use crate::params::ReadParams;
    use crate::params::SetTypeParams;
    use borer_engine::program::{Arch, Program, Section};
    use rmcp::handler::server::wrapper::Parameters;
    let mut bytes = vec![0u8; 0x200];
    bytes[0x100..0x104].copy_from_slice(&7u32.to_le_bytes());
    bytes[0x104..0x108].copy_from_slice(b"hi\0\0");
    bytes[0x108..0x10c].copy_from_slice(&9u32.to_le_bytes());
    bytes[0x10c..0x110].copy_from_slice(b"yo\0\0");
    let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
    let program = Program::raw(bytes, Arch::X86_64, 0, None, vec![data]);
    let server = crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    };
    server
        .set_type(Parameters(SetTypeParams {
            name: Some("Item".to_owned()),
            fields: Some(vec!["0:id:u32".to_owned(), "4:tag:char[4]".to_owned()]),
            values: None,
            size: None,
            address: None,
            r#type: None,
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect("defines");
    let read = |kind: Option<ReadKind>, ty: &str, address: &str, count: Option<u32>| {
        server.read(Parameters(ReadParams {
            address: address.to_owned(),
            kind,
            r#type: Some(ty.to_owned()),
            count,
        }))
    };
    let text = read(None, "Item", "0x2000", Some(2)).expect("reads");
    assert!(
        text.starts_with("# showing 4 of 4 rows: Item[2] at 0x2000 in .data, 0x10 bytes\n"),
        "{text}"
    );
    assert!(
        text.contains("0x2004       [0].tag char[4] \"hi\"\n"),
        "{text}"
    );
    assert!(
        text.contains("0x2008       [1].id  u32     0x9\n"),
        "{text}"
    );
    let one = read(None, "Item", "0x2008", None).expect("reads one");
    assert!(one.contains("0x200c       tag char[4] \"yo\"\n"), "{one}");
    let both = read(Some(ReadKind::U8), "Item", "0x2000", None).expect_err("kind and type");
    assert!(both.message.contains("give one"), "{}", both.message);
    let off = read(None, "Item", "off:0x100", None).expect_err("an offset");
    assert!(off.message.contains("takes an address"), "{}", off.message);
    let bad = read(None, "Item[", "0x2000", None).expect_err("an open bracket");
    assert!(bad.message.contains("does not close"), "{}", bad.message);
}

/// `set_type` with `values` defines an enum, applies it at a data
/// global, and `types` lists its values in value order.
///
/// A value under two names, and fields stated beside values, are
/// refused with a message naming the offender.
///
/// # Panics
///
/// When the listing misses the enum, or a refusal accepts.
#[test]
fn set_type_defines_enums_and_refuses() {
    use crate::params::SetTypeParams;
    use crate::params::TypesParams;
    use borer_engine::program::{Arch, Program, Section};
    use rmcp::handler::server::wrapper::Parameters;
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
    let program = Program::raw(
        vec![0xcc; 0x200],
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![text, data],
    );
    let server = crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    };
    let out = server
        .set_type(Parameters(SetTypeParams {
            name: Some("State".to_owned()),
            fields: None,
            values: Some(vec!["Run:1".to_owned(), "Idle:0".to_owned()]),
            size: None,
            address: Some("0x2000".to_owned()),
            r#type: Some("State".to_owned()),
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect("defines and applies");
    assert!(
        out.contains("defined enum State: 2 value(s), 0x4 byte(s)"),
        "{out}"
    );
    assert!(
        out.contains("applied State at 0x2000 (4 byte(s)); decompile names its values"),
        "{out}"
    );
    let listed = server
        .types(Parameters(TypesParams {
            filter: Some("state".to_owned()),
            offset: None,
            limit: None,
            count_only: None,
        }))
        .expect("lists");
    assert!(
        listed.contains("enum\tState\t0x4\tIdle = 0, Run = 1"),
        "{listed}"
    );
    assert!(listed.contains("applied\t0x2000\t-\tState"), "{listed}");
    let bad = server
        .set_type(Parameters(SetTypeParams {
            name: Some("Bad".to_owned()),
            fields: None,
            values: Some(vec!["A:0".to_owned(), "B:0".to_owned()]),
            size: None,
            address: None,
            r#type: None,
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect_err("a duplicate value refused");
    assert!(
        bad.message.contains("names value 0 twice"),
        "{}",
        bad.message
    );
    let bad = server
        .set_type(Parameters(SetTypeParams {
            name: Some("Bad".to_owned()),
            fields: Some(vec!["0x0:f:u32".to_owned()]),
            values: Some(vec!["A:0".to_owned()]),
            size: None,
            address: None,
            r#type: None,
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
        .expect_err("fields beside values refused");
    assert!(
        bad.message.contains("both fields and values"),
        "{}",
        bad.message
    );
}

/// `set_type` refuses a type with more pointers than the language
/// holds, on a dry run too, rather than building a chain of boxes whose
/// spelling and drop overflowed the stack and took the server down.
///
/// # Panics
///
/// When a deep type is accepted or the refusal does not say why.
#[test]
fn set_type_refuses_a_type_too_deep_to_walk() {
    use crate::params::SetTypeParams;
    use borer_engine::program::{Arch, Program, Section};
    use rmcp::handler::server::wrapper::Parameters;
    let data = Section::mapped(".data", 0x2000, 0, 0x100, true, false);
    let program = Program::raw(vec![0; 0x100], Arch::X86_64, 0, None, vec![data]);
    let server = crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    };
    let refuse = |name: Option<&str>, address: Option<&str>, ty: &str| {
        server
            .set_type(Parameters(SetTypeParams {
                name: name.map(str::to_owned),
                fields: None,
                values: None,
                size: None,
                address: address.map(str::to_owned),
                r#type: Some(ty.to_owned()),
                dry_run: None,
                ..SetTypeParams::default()
            }))
            .expect_err("a type too deep to walk was accepted")
            .message
    };
    let deep = format!("u8 {}", "*".repeat(17));
    let long = format!("u8 {}", "*".repeat(20_000));
    for (name, address) in [(Some("Stars"), None), (None, Some("0x2000"))] {
        let refused = refuse(name, address, &deep);
        assert!(refused.contains("stacks 17 pointers"), "{refused}");
        let refused = refuse(name, address, &long);
        assert!(
            refused.contains("the type is 20003 characters"),
            "{refused}"
        );
    }
}

/// `set_type` at a function states its prototype, and with `var` one of
/// its variables.
///
/// Dry runs leave the overlay's fingerprint as it was; applying states
/// the prototype, and a variable is then found by the name the
/// prototype gave it; a register and a data address are refused.
///
/// # Panics
///
/// When a dry run writes, an application does not, or a refusal is
/// accepted.
#[test]
fn set_type_states_prototypes_and_variables() {
    use crate::params::SetTypeParams;
    use borer_engine::analysis::protos::VarKey;
    use borer_engine::program::{Arch, Program, Section};
    use rmcp::handler::server::wrapper::Parameters;
    let mut bytes = vec![0xcc; 0x200];
    // ASM: lea eax, [rcx+1]; ret
    bytes[..4].copy_from_slice(&[0x8d, 0x41, 0x01, 0xc3]);
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
    let program = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text, data]);
    let server = crate::BorerServer {
        program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(program)))),
        pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
        ..crate::BorerServer::default()
    };
    let call = |address: &str,
                ty: Option<&str>,
                var: Option<&str>,
                name: Option<&str>,
                dry: Option<bool>| {
        server.set_type(Parameters(SetTypeParams {
            name: name.map(str::to_owned),
            fields: None,
            values: None,
            size: None,
            address: Some(address.to_owned()),
            r#type: ty.map(str::to_owned),
            var: var.map(str::to_owned),
            dry_run: dry,
            ..SetTypeParams::default()
        }))
    };
    let before = server.overlay_plain().fingerprint();
    let out = call("0x1000", Some("int f(int n)"), None, None, None).expect("dry-runs");
    assert!(
        out.starts_with("dry-run: would state sub_1000 (0x1000) as int (int n)"),
        "{out}"
    );
    assert_eq!(server.overlay_plain().fingerprint(), before);
    let out = call("0x1002", Some("int f(int n)"), None, None, Some(false)).expect("states");
    assert!(
        out.contains("stated sub_1000 (0x1000) as int (int n)"),
        "{out}"
    );
    let stated = server.overlay_plain().fingerprint();
    assert_ne!(stated, before);
    let out = call("0x1000", Some("Mystery *"), Some("n"), Some("thing"), None)
        .expect("dry-runs the variable");
    assert!(
        out.starts_with("dry-run: would name a1 of sub_1000 (0x1000) Mystery *thing"),
        "{out}"
    );
    assert_eq!(server.overlay_plain().fingerprint(), stated);
    call("0x1000", None, Some("n"), Some("count"), Some(false)).expect("names");
    let o = server.overlay_plain();
    assert_eq!(
        o.vars
            .get(&0x1000)
            .and_then(|v| v.get(&VarKey::Param(0)))
            .map(|v| v.name.as_str()),
        Some("count")
    );
    let refused = call("0x1000", None, Some("rax"), Some("x"), None)
        .expect_err("a register was named")
        .message;
    assert!(refused.contains("register"), "{refused}");
    let refused = call("0x2000", None, Some("a1"), Some("x"), None)
        .expect_err("a variable outside any function was named")
        .message;
    assert!(refused.contains("function"), "{refused}");
    let refused = call("0x1000", None, Some("a3"), Some("x"), None)
        .expect_err("a parameter the function does not take was named")
        .message;
    assert!(
        refused.starts_with("sub_1000 has no variable a3"),
        "{refused}"
    );
    let refused = call("0x1000", Some("int f(int n"), None, None, None)
        .expect_err("a prototype with an open parameter list was stated")
        .message;
    assert!(refused.contains("parameter list"), "{refused}");
    let refused = call("0x1000", Some("u32"), None, None, None)
        .expect_err("a plain type was stated at a function")
        .message;
    assert!(refused.contains("types apply to data globals"), "{refused}");
}

/// `set_comment` refuses an address in no section as `set_name` does,
/// dry run or not, and still previews one inside a section.
///
/// # Panics
///
/// When a comment outside the image is accepted, the two refusals
/// differ beyond the annotation's name, or a mapped address is refused.
#[test]
fn a_comment_outside_every_section_is_refused_as_a_name_is() {
    use crate::params::SetCommentParams;
    use crate::params::SetNameParams;
    use rmcp::handler::server::wrapper::Parameters;
    let server = raw_server();
    let comment = |address: &str, dry_run| {
        server.set_comment(Parameters(SetCommentParams {
            address: address.to_owned(),
            comment: "typo".to_owned(),
            dry_run,
        }))
    };
    let refused = comment("0x1", Some(false)).expect_err("outside the image");
    assert!(
        refused
            .message
            .starts_with("0x1 is in no section, so nothing there can take a comment; "),
        "{}",
        refused.message
    );
    assert!(comment("0x1", None).is_err(), "a dry run is refused too");
    let named = server
        .set_name(Parameters(SetNameParams {
            address: Some("0x1".to_owned()),
            name: Some("typo".to_owned()),
            names: None,
            force: None,
            dry_run: None,
        }))
        .expect_err("outside the image");
    assert_eq!(named.code, refused.code);
    assert_eq!(
        named.message,
        refused.message.replace("a comment", "a name")
    );
    let preview = comment("0x1010", None).expect("inside .text");
    assert!(
        preview.starts_with("dry-run: would set comment at 0x1010"),
        "{preview}"
    );
    assert!(crate::state::read_lock(&server.overlay).comments.is_empty());
}

/// `set_type` refuses a struct that would hold itself by value through
/// another, stated field by field or in C, as a project holding it is
/// refused on load.
///
/// The structured form took it, the sizes agreeing, and left the session a
/// type no layout sizes and its saved project could not load.
///
/// # Panics
///
/// When the cycle is accepted either way, or the refusal does not name
/// it.
#[test]
fn set_type_refuses_a_struct_holding_itself_by_value() {
    use crate::params::SetTypeParams;
    use rmcp::handler::server::wrapper::Parameters;
    let server = raw_server();
    let state = |name: Option<&str>, field: Option<&str>, ty: Option<&str>| {
        server.set_type(Parameters(SetTypeParams {
            name: name.map(str::to_owned),
            fields: field.map(|f| vec![f.to_owned()]),
            r#type: ty.map(str::to_owned),
            dry_run: Some(false),
            ..SetTypeParams::default()
        }))
    };
    state(Some("S"), Some("0x0:a:u32"), None).expect("S is a u32");
    state(Some("B"), Some("0x0:s:S"), None).expect("B holds S");
    for refused in [
        state(Some("S"), Some("0x0:b:B"), None),
        state(None, None, Some("struct S { B b; };")),
    ] {
        let why = refused.expect_err("S holds itself through B").message;
        assert!(why.contains("holds itself by value (B -> S -> B)"), "{why}");
    }
}
