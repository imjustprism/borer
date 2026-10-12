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
