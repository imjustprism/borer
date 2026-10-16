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
        ("partial", "no partial product check"),
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

/// A two-byte cell.
///
/// # Arguments
///
/// * `v` - The value.
fn cell(v: u16) -> [u8; 2] {
    v.to_le_bytes()
}

/// Appends a name to a `#Strings` heap and returns its index as a cell.
///
/// # Arguments
///
/// * `heap` - The heap, its empty string first.
/// * `text` - The name.
fn name(heap: &mut Vec<u8>, text: &str) -> [u8; 2] {
    let at = u16::try_from(heap.len()).expect("a small heap");
    heap.extend_from_slice(text.as_bytes());
    heap.push(0);
    cell(at)
}

/// Pads bytes to a four-byte boundary.
///
/// # Arguments
///
/// * `b` - The bytes.
fn padded(mut b: Vec<u8>) -> Vec<u8> {
    b.resize(b.len().next_multiple_of(4), 0);
    b
}

/// A PE32+ .NET assembly with an IL method and a P/Invoke.
///
/// `Ns.Program::Main` is an IL body at RVA 0x1050 and
/// `Ns.Program::MessageBox` a P/Invoke of `user32.dll!MessageBoxW`; one
/// user string holds a URL. The CLR header is at 0x1010 and the metadata
/// at 0x1080, in [`tiny_pe`]'s `.text` grown to 0x400 bytes.
fn dotnet_pe() -> Vec<u8> {
    let mut s = vec![0u8];
    let mut t: Vec<u8> = Vec::new();
    let lone = name(&mut s, "<Module>");
    let (program, ns) = (name(&mut s, "Program"), name(&mut s, "Ns"));
    let (main, pinvoke) = (name(&mut s, "Main"), name(&mut s, "MessageBox"));
    let (user32, entry) = (name(&mut s, "user32.dll"), name(&mut s, "MessageBoxW"));
    let none = 0u32.to_le_bytes();
    let rows: [&[&[u8]]; 6] = [
        &[&none, &lone, &cell(0), &cell(0), &cell(1), &cell(1)],
        &[&none, &program, &ns, &cell(0), &cell(1), &cell(1)],
        &[
            &0x1050u32.to_le_bytes(),
            &cell(0),
            &cell(0x96),
            &main,
            &cell(0),
            &cell(1),
        ],
        &[
            &none,
            &cell(0x80),
            &cell(0x2096),
            &pinvoke,
            &cell(0),
            &cell(1),
        ],
        &[&user32],
        &[&cell(0x104), &cell((2 << 1) | 1), &entry, &cell(1)],
    ];
    for row in rows {
        for c in row {
            t.extend_from_slice(c);
        }
    }
    let counts: [(u32, u32); 4] = [(0x02, 2), (0x06, 2), (0x1a, 1), (0x1c, 1)];
    let mut stream = vec![0, 0, 0, 0, 2, 0, 0, 1];
    let valid = counts.iter().fold(0u64, |v, (table, _)| v | (1 << table));
    stream.extend_from_slice(&valid.to_le_bytes());
    stream.extend_from_slice(&0u64.to_le_bytes());
    for (_, n) in counts {
        stream.extend_from_slice(&n.to_le_bytes());
    }
    stream.extend_from_slice(&t);
    let url: Vec<u8> = "http://c2.example.test/gate.php"
        .encode_utf16()
        .flat_map(u16::to_le_bytes)
        .collect();
    let mut us = vec![0, u8::try_from(url.len() + 1).expect("a short string")];
    us.extend_from_slice(&url);
    us.push(0);
    let streams = [
        ("#~", padded(stream)),
        ("#Strings", padded(s)),
        ("#US", padded(us)),
    ];
    let mut meta = b"BSJB\x01\0\x01\0\0\0\0\0\x0c\0\0\0v4.0.30319\0\0\0\0".to_vec();
    meta.extend_from_slice(&cell(3));
    let mut off = meta.len()
        + streams
            .iter()
            .map(|(n, _)| 8 + (n.len() + 4) / 4 * 4)
            .sum::<usize>();
    let mut body = Vec::new();
    for (stream_name, bytes) in &streams {
        meta.extend_from_slice(&u32::try_from(off).expect("fits").to_le_bytes());
        meta.extend_from_slice(&u32::try_from(bytes.len()).expect("fits").to_le_bytes());
        meta.extend_from_slice(&padded([stream_name.as_bytes(), b"\0"].concat()));
        body.extend_from_slice(bytes);
        off += bytes.len();
    }
    meta.extend_from_slice(&body);
    let mut b = tiny_pe();
    let (opt, row) = (0x80 + 24, 0x80 + 24 + 0xf0);
    b[opt + 112 + 14 * 8..opt + 112 + 15 * 8].copy_from_slice(&[0x10, 0x10, 0, 0, 72, 0, 0, 0]);
    b[row + 8..row + 12].copy_from_slice(&0x400u32.to_le_bytes());
    b[row + 16..row + 20].copy_from_slice(&0x400u32.to_le_bytes());
    b.resize(0x600, 0);
    let mut cor20 = vec![72, 0, 0, 0, 2, 0, 5, 0, 0x80, 0x10, 0, 0];
    cor20.extend_from_slice(&u32::try_from(meta.len()).expect("fits").to_le_bytes());
    cor20.extend_from_slice(&1u32.to_le_bytes());
    cor20.extend_from_slice(&0x0600_0001u32.to_le_bytes());
    b[0x210..0x210 + cor20.len()].copy_from_slice(&cor20);
    // ASM: a tiny IL header (2 bytes of code), nop, ret.
    b[0x250..0x253].copy_from_slice(&[0x0a, 0x00, 0x2a]);
    b[0x280..0x280 + meta.len()].copy_from_slice(&meta);
    b
}

/// A .NET assembly's metadata and user strings read over the protocol.
///
/// `borer://clr` lists the P/Invoke, the user string joins `strings` whole
/// as `dotnet-us`, `borer://iocs` reads the URL in it from that source,
/// and `binary_info` has a `.net:` line.
#[test]
fn a_dotnet_assembly_lists_its_metadata_and_user_strings() {
    let file = std::env::temp_dir().join(format!("borer_dotnet_{}.exe", std::process::id()));
    std::fs::write(&file, dotnet_pe()).expect("the fixture is writable");
    let mut client = Client::start(&file.to_string_lossy());
    let pinvokes = read(&mut client, "borer://clr/pinvoke").expect("answers");
    let strings = client.text("strings", r#"{"encoding": "utf16"}"#);
    let iocs = read(&mut client, "borer://iocs/url").expect("answers");
    let info = client.text("binary_info", "{}");
    client.finish();
    std::fs::remove_file(&file).ok();
    assert!(
        pinvokes
            .contains("\npinvoke\t0x06000002\t-\tNs.Program::MessageBox\tuser32.dll!MessageBoxW\n"),
        "{pinvokes}"
    );
    assert!(
        strings.contains(" 31 dotnet-us \"http://c2.example.test/gate.php\"\n"),
        "{strings}"
    );
    assert!(
        iocs.lines()
            .any(|l| l.contains("dotnet-us") && l.contains("http://c2.example.test/gate.php")),
        "{iocs}"
    );
    assert!(
        info.contains(".net:    module -, runtime 2.5, metadata v4.0.30319, ilonly; entry 0x06000001 Ns.Program::Main;"),
        "{info}"
    );
}
