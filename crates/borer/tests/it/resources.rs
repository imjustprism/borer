//! The resources over JSON-RPC stdio on the real binary
//! (`CARGO_BIN_EXE_borer`): every template read without its argument
//! says how to read it, and the example it gives reads.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
#![expect(
    clippy::expect_used,
    clippy::panic,
    reason = "a server that cannot be driven has no useful recovery in a test client"
)]

use crate::contract::tiny_pe;
use crate::reload::Client;

/// Reads a URI through `resources/read`.
///
/// # Arguments
///
/// * `client` - The session.
/// * `uri` - The URI.
///
/// # Returns
///
/// The text.
///
/// # Errors
///
/// The error's message, when the server refuses the URI.
fn read(client: &mut Client, uri: &str) -> Result<String, String> {
    let params = serde_json::json!({ "uri": uri }).to_string();
    let line = client.call("resources/read", &params);
    let reply: serde_json::Value = serde_json::from_str(&line).expect("a reply is JSON");
    match reply["result"]["contents"][0]["text"].as_str() {
        Some(text) => Ok(text.to_owned()),
        None => Err(reply["error"]["message"]
            .as_str()
            .unwrap_or_else(|| panic!("neither text nor an error: {line}"))
            .to_owned()),
    }
}

/// The URIs a list method answers, from the field each entry carries them in.
///
/// # Arguments
///
/// * `client` - The session.
/// * `method` - `resources/list` or `resources/templates/list`.
/// * `list` - The array the result holds them in.
/// * `field` - The field of each entry holding the URI.
fn listed(client: &mut Client, method: &str, list: &str, field: &str) -> Vec<String> {
    let line = client.call(method, "{}");
    let reply: serde_json::Value = serde_json::from_str(&line).expect("a reply is JSON");
    reply["result"][list]
        .as_array()
        .unwrap_or_else(|| panic!("no {list}: {line}"))
        .iter()
        .filter_map(|t| t[field].as_str().map(str::to_owned))
        .collect()
}

/// Every template read without its argument gives an example, and the
/// example reads.
///
/// A template a fixed resource shares a name with is asked through
/// `borer://help/`. Its example, built from the loaded binary, answers, or
/// it is refused for what the one-function fixture lacks, named here with
/// the words the refusal says, and never as a URI or a spec the server
/// cannot read.
#[test]
fn every_template_example_reads() {
    /// Templates whose example the fixture cannot answer, each with what
    /// the refusal says: a file the example names that is not there, or a
    /// structure a lone `ret` does not have.
    const LACKING: &[(&str, &str)] = &[
        ("flat", "no flattening dispatch"),
        ("solve", "takes no parameters"),
        ("vm", "no dispatch loop"),
        ("script", "scan.rhai"),
        ("anchors", "client.anchors"),
        ("changes", "before.snapshot"),
    ];
    let file = std::env::temp_dir().join(format!("borer_examples_{}.exe", std::process::id()));
    std::fs::write(&file, tiny_pe()).expect("the fixture is writable");
    let mut client = Client::start(&file.to_string_lossy());
    let fixed = listed(&mut client, "resources/list", "resources", "uri");
    let templates = listed(
        &mut client,
        "resources/templates/list",
        "resourceTemplates",
        "uriTemplate",
    );
    let mut failures = Vec::new();
    for template in &templates {
        let name = template
            .strip_prefix("borer://")
            .and_then(|path| path.split('/').next())
            .unwrap_or_else(|| panic!("not a borer URI: {template}"));
        let bare = if fixed.iter().any(|f| f == &format!("borer://{name}")) {
            format!("borer://help/{name}")
        } else {
            format!("borer://{name}")
        };
        let help = read(&mut client, &bare).unwrap_or_else(|e| panic!("{bare}: {e}"));
        assert!(help.contains(&format!("# {template}\n")), "{help}");
        let example = help
            .lines()
            .find_map(|l| l.strip_prefix("# example: "))
            .unwrap_or_else(|| panic!("{bare} gives no example: {help}"))
            .to_owned();
        let lacking = LACKING.iter().find(|(n, _)| *n == name);
        match (read(&mut client, &example), lacking) {
            (Ok(_), None) => {}
            (Err(e), Some((_, says))) if e.contains(says) => {}
            (outcome, _) => failures.push(format!("{example}: {outcome:?}")),
        }
    }
    client.finish();
    std::fs::remove_file(&file).ok();
    assert!(failures.is_empty(), "{failures:#?}");
}

/// `borer://session` lists what the session did.
///
/// That is the load and the comment it applied, not the name it only
/// tried, the open question in the overlay, which is not saved, and each
/// request it answered with the flags it earned: a page asked for is
/// listed with its page, as capped and paged.
#[test]
fn the_session_ledger_lists_what_the_session_did() {
    let file = std::env::temp_dir().join(format!("borer_session_{}.exe", std::process::id()));
    std::fs::write(&file, tiny_pe()).expect("the fixture is writable");
    let mut client = Client::start(&file.to_string_lossy());
    client.text(
        "set_comment",
        r#"{"address":"0x140001000","comment":"?what does it return","dry_run":false}"#,
    );
    client.text("set_name", r#"{"address":"0x140001000","name":"tried"}"#);
    let page = read(&mut client, "borer://help!offset=2!limit=2").expect("pages");
    assert!(page.starts_with("# showing 2 of "), "{page}");
    assert!(
        page.contains("borer://help!limit=2!offset=4 for the next page"),
        "{page}"
    );
    let session = read(&mut client, "borer://session").expect("answers");
    client.finish();
    std::fs::remove_file(&file).ok();
    assert!(
        session.starts_with("# session: borer_session_"),
        "{session}"
    );
    assert!(session.contains("\nload_binary {"), "{session}");
    assert!(
        session.contains("\nset_comment {\"address\":\"0x140001000\",\"comment\":\"?what does it return\",\"dry_run\":false}\n"),
        "{session}"
    );
    assert!(!session.contains("\nset_name {"), "a dry run: {session}");
    assert!(
        session.contains("1 comments (1 open questions)") && session.contains("not saved"),
        "{session}"
    );
    assert!(
        session.contains("capped paged  borer://help!offset=2!limit=2\n"),
        "{session}"
    );
    assert!(
        session.contains("set_name {\"address\":\"0x140001000\",\"name\":\"tried\"}\n"),
        "an answer: {session}"
    );
    assert!(!session.contains("borer://session"), "{session}");
}

/// A program embedded in a file is listed by `borer://children`, opens
/// with `load_binary` on `<file>@<offset>` as a program of its own, and
/// `binary_info` then names the file and offset it came from.
#[test]
fn an_embedded_program_opens_and_names_its_parent() {
    let file = std::env::temp_dir().join(format!("borer_children_{}.bin", std::process::id()));
    let mut blob = vec![0u8; 0x200];
    blob.extend_from_slice(&tiny_pe());
    std::fs::write(&file, &blob).expect("the fixture is writable");
    let shown = file.to_string_lossy().to_string();
    let mut client = Client::start(&shown);
    let children = read(&mut client, "borer://children").expect("answers");
    let child = format!("{shown}@0x200");
    let loaded = client.text(
        "load_binary",
        &serde_json::json!({ "path": child }).to_string(),
    );
    let info = client.text("binary_info", "{}");
    client.finish();
    std::fs::remove_file(&file).ok();
    assert!(
        children.contains("\n0x200\t0x400\tpe\tPE32+ x86-64 exe, console, 1 section\n"),
        "{children}"
    );
    assert!(
        children.contains(&format!("load_binary path={shown}@<off>")),
        "{children}"
    );
    let parent = format!("parent:  {shown} at file offset 0x200, 0x400 bytes\n");
    assert!(loaded.contains(&parent), "{loaded}");
    assert!(info.contains(&parent), "{info}");
    assert!(info.contains("format:  PE"), "{info}");
}
