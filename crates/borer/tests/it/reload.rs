//! The reload hand-over, driven over JSON-RPC stdio on the real binary
//! (`CARGO_BIN_EXE_borer`).

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
#![expect(
    clippy::expect_used,
    clippy::panic,
    reason = "a server that cannot be driven has no useful recovery in a test client"
)]

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{Receiver, channel};
use std::time::Duration;

/// A client on the server's pipes, reading replies on a thread so a lost
/// reply is a failure after a timeout rather than a hang.
struct Client {
    /// The process the client launched, as a host launches its server: the
    /// relay, which must serve the whole session through every reload.
    child: Child,
    /// The server's standard input.
    stdin: ChildStdin,
    /// Every line the pipe carries, from a reader thread.
    lines: Receiver<String>,
    /// The lines read while waiting for a reply that were not it:
    /// notifications and other replies.
    passed: Vec<String>,
    /// The last request id used.
    id: u64,
}

impl Client {
    /// Longest wait for one reply; the analysis of this binary is the
    /// slowest thing a reply here waits for.
    const REPLY: Duration = Duration::from_secs(300);

    /// Starts the server, initializes the session and loads `load`.
    ///
    /// # Arguments
    ///
    /// * `load` - The file the session loads.
    fn start(load: &str) -> Client {
        let exe = env!("CARGO_BIN_EXE_borer");
        let mut child = Command::new(exe)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn borer.exe");
        let stdin = child.stdin.take().expect("stdin is piped");
        let stdout = child.stdout.take().expect("stdout is piped");
        let (tx, lines) = channel();
        std::thread::spawn(move || {
            for line in BufReader::new(stdout).lines().map_while(Result::ok) {
                if tx.send(line).is_err() {
                    break;
                }
            }
        });
        let mut client = Client {
            child,
            stdin,
            lines,
            passed: Vec::new(),
            id: 0,
        };
        client.call(
            "initialize",
            r#"{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"t","version":"0"}}"#,
        );
        client.write(r#"{"jsonrpc":"2.0","method":"notifications/initialized"}"#);
        let loaded = client.tool("load_binary", &format!(r#"{{"path":{load:?}}}"#));
        assert!(loaded.contains("\"result\""), "{loaded}");
        client
    }

    /// Writes one or more lines to the server in one write, so lines
    /// pipelined together reach the pipe together.
    ///
    /// # Arguments
    ///
    /// * `lines` - JSON-RPC messages, one a line, without the last newline.
    fn write(&mut self, lines: &str) {
        self.stdin
            .write_all(format!("{lines}\n").as_bytes())
            .expect("the server reads");
        self.stdin.flush().expect("the pipe takes the line");
    }

    /// Returns the next line the server writes that contains `tag`, keeping
    /// the lines before it in [`Client::passed`].
    ///
    /// # Arguments
    ///
    /// * `tag` - Text the line carries.
    /// * `what` - What the line is, for the failure message.
    fn next_with(&mut self, tag: &str, what: &str) -> String {
        loop {
            let line = self
                .lines
                .recv_timeout(Self::REPLY)
                .unwrap_or_else(|_| panic!("no {what} within {:?}", Self::REPLY));
            if line.contains(tag) {
                return line;
            }
            self.passed.push(line);
        }
    }

    /// Sends a request and returns its reply line, skipping the
    /// notifications and other replies in between.
    ///
    /// # Arguments
    ///
    /// * `method` - The JSON-RPC method.
    /// * `params` - Its params, as JSON.
    fn call(&mut self, method: &str, params: &str) -> String {
        self.id += 1;
        let id = self.id;
        self.write(&format!(
            r#"{{"jsonrpc":"2.0","id":{id},"method":"{method}","params":{params}}}"#
        ));
        self.next_with(
            &format!("\"id\":{id},"),
            &format!("reply to {method} (id {id})"),
        )
    }

    /// Calls a tool and returns the reply line.
    ///
    /// # Arguments
    ///
    /// * `name` - The tool.
    /// * `arguments` - Its arguments, as a JSON object.
    fn tool(&mut self, name: &str, arguments: &str) -> String {
        self.call(
            "tools/call",
            &format!(r#"{{"name":"{name}","arguments":{arguments}}}"#),
        )
    }

    /// Calls a tool and returns the text it answered.
    ///
    /// # Arguments
    ///
    /// * `name` - The tool.
    /// * `arguments` - Its arguments, as a JSON object.
    fn text(&mut self, name: &str, arguments: &str) -> String {
        let line = self.tool(name, arguments);
        let reply: serde_json::Value = serde_json::from_str(&line).expect("a reply is JSON");
        reply["result"]["content"][0]["text"]
            .as_str()
            .unwrap_or_else(|| panic!("{name} answered no text: {line}"))
            .to_owned()
    }

    /// Fails unless the process the client launched is still running, as a
    /// host requires of the server it launched.
    ///
    /// # Arguments
    ///
    /// * `when` - The point of the session, for the failure message.
    fn still_running(&mut self, when: &str) {
        let exited = self.child.try_wait().expect("the process can be polled");
        assert!(
            exited.is_none(),
            "the launched process {} exited {when}: {exited:?}; a host would start a fresh server",
            self.child.id()
        );
    }

    /// Ends the session as a host does, by closing the server's input, and
    /// fails unless the launched process then exits successfully.
    fn finish(self) {
        let Client {
            mut child, stdin, ..
        } = self;
        drop(stdin);
        let status = child.wait().expect("the launched process exits");
        assert!(status.success(), "{status}");
    }
}

/// A request sent as soon as the reload reply arrives is answered, by the
/// server taking over.
///
/// The old process kept reading its standard input for half a second after
/// answering, so a request arriving in that window was read by a process
/// about to exit: one its analysis could not answer in time was lost, and
/// the client waited for a reply that never came. `functions` on this
/// binary is such a request. Now the relay passes nothing on after the
/// reload request until the old worker has ended, and gives the request to
/// the new one.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn a_request_sent_right_after_the_reload_reply_is_answered() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let mut client = Client::start(exe);
    let reload = client.tool("reload", "{}");
    assert!(reload.contains("reloading borer"), "{reload}");
    let functions = client.tool("functions", r#"{"count_only":true}"#);
    assert!(
        functions.contains("# ") && functions.contains(" functions"),
        "{functions}"
    );
    let info = client.tool("binary_info", "{}");
    assert!(info.contains("arch: x86-64"), "{info}");
    client.finish();
}

/// Two requests the client pipelines, the reload and one behind it in the
/// same write, are both answered: the relay holds the one behind the reload
/// and the new worker answers it.
///
/// The held request is `annotations`, long enough to carry its tag. Once a
/// comment is added, the same request with that tag is answered by the
/// lines that changed, which only the worker that sent the held answer can
/// compute: that is how the test sees that the new worker, not the old,
/// had it.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn a_request_pipelined_behind_the_reload_is_answered() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let mut client = Client::start(exe);
    let info = client.text("binary_info", "{}");
    let entry = info
        .split("entry: 0x")
        .nth(1)
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|hex| u64::from_str_radix(hex, 16).ok())
        .unwrap_or_else(|| panic!("no entry in {info}"));
    let comment = |client: &mut Client, va: u64, text: &str| {
        let set = client.text(
            "set_comment",
            &format!(r#"{{"address":"{va:#x}","comment":"{text}","dry_run":false}}"#),
        );
        assert!(set.contains("comment set"), "{set}");
    };
    for va in entry..entry + 3 {
        comment(&mut client, va, &"x".repeat(200));
    }
    client.id += 1;
    let reload_id = client.id;
    client.id += 1;
    let held_id = client.id;
    client.write(&format!(
        r#"{{"jsonrpc":"2.0","id":{reload_id},"method":"tools/call","params":{{"name":"reload","arguments":{{}}}}}}
{{"jsonrpc":"2.0","id":{held_id},"method":"tools/call","params":{{"name":"annotations","arguments":{{}}}}}}"#
    ));
    let mut held = None;
    let mut reloaded = false;
    while held.is_none() || !reloaded {
        let line = client
            .lines
            .recv_timeout(Client::REPLY)
            .expect("both replies arrive");
        if line.contains(&format!("\"id\":{reload_id},")) {
            assert!(line.contains("reloading borer"), "{line}");
            reloaded = true;
        } else if line.contains(&format!("\"id\":{held_id},")) {
            let reply: serde_json::Value = serde_json::from_str(&line).expect("a reply is JSON");
            held = reply["result"]["content"][0]["text"]
                .as_str()
                .map(str::to_owned);
            assert!(held.is_some(), "{line}");
        }
    }
    let held = held.unwrap_or_default();
    let tag = held
        .lines()
        .last()
        .and_then(|l| l.strip_prefix("# since="))
        .unwrap_or_else(|| panic!("the held answer carries no tag: {held}"))
        .to_owned();
    comment(&mut client, entry + 3, "held");
    let after = client.text("annotations", &format!(r#"{{"since":"{tag}"}}"#));
    assert!(
        after.starts_with(&format!("# changed since the answer tagged {tag}: ")),
        "{after}"
    );
    client.finish();
}

/// The process a host launched serves the whole session, through two
/// reloads, with the loaded file and a name set before the first.
///
/// A host takes the end of the process it launched for the end of the
/// server, and starts a fresh one with nothing loaded: the hand-over that
/// exited the launched process once its child had the pipes worked for a
/// client that kept writing to them, but under such a host the next call
/// answered "no binary loaded". The relay keeps the launched process up and
/// replaces only the worker behind it, which announces the tools again.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn the_launched_process_serves_the_session_through_reloads() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let mut client = Client::start(exe);
    let info = client.text("binary_info", "{}");
    let entry = info
        .split("entry: ")
        .nth(1)
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap_or_else(|| panic!("no entry in {info}"))
        .to_owned();
    let named = client.text(
        "set_name",
        &format!(r#"{{"address":"{entry}","name":"kept_across_reload","dry_run":false}}"#),
    );
    assert!(named.contains("-> kept_across_reload"), "{named}");
    for round in ["the first reload", "the second reload"] {
        client.passed.clear();
        let reload = client.text("reload", "{}");
        assert!(reload.contains("reloading borer"), "{reload}");
        client.still_running(&format!("on answering {round}"));
        client.next_with(
            "notifications/tools/list_changed",
            &format!("tool list announced after {round}"),
        );
        let after = client.text("binary_info", "{}");
        assert_eq!(after, info, "the file loaded before {round}");
        let names = client.text("annotations", "{}");
        assert!(
            names.contains(&format!("{entry:<12} name: kept_across_reload")),
            "the name set before {round}: {names}"
        );
        client.still_running(&format!("after {round}"));
    }
    client.finish();
}

/// A reload loads the file the way it was loaded.
///
/// It keeps the `pdb` and the `entry_file_offset` the session gave, the offset
/// mapped to its address through the section table. The hand-over loaded with
/// the defaults, so a session that had turned the PDB off or moved the entry
/// got them back, and the offset was added to the image base as if it were an
/// address.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn a_reload_keeps_the_load_options() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let mut client = Client::start(exe);
    let info = client.text("binary_info", "{}");
    let text = info
        .lines()
        .find(|l| l.trim_start().starts_with(".text "))
        .unwrap_or_else(|| panic!("no .text row in {info}"));
    let hex = |field: Option<&str>| {
        field
            .and_then(|f| f.strip_prefix("0x"))
            .and_then(|f| u64::from_str_radix(f, 16).ok())
            .unwrap_or_else(|| panic!("no number in {text}"))
    };
    let mut fields = text.split_whitespace().skip(1);
    let va = hex(fields.next());
    let off = hex(fields.nth(1));
    let loaded = client.text(
        "load_binary",
        &format!(
            r#"{{"path":{exe:?},"pdb":false,"entry_file_offset":{}}}"#,
            off + 0x10
        ),
    );
    let entry = format!("entry: {:#x}", va + 0x10);
    assert!(loaded.contains(&entry), "{entry} not in {loaded}");
    assert!(!loaded.contains("pdb:"), "{loaded}");
    let before = client.text("binary_info", "{}");
    client.passed.clear();
    let reload = client.text("reload", "{}");
    assert!(reload.contains("reloading borer"), "{reload}");
    client.next_with(
        "notifications/tools/list_changed",
        "tool list announced after the reload",
    );
    let after = client.text("binary_info", "{}");
    assert_eq!(after, before, "the reload loaded the file another way");
    client.finish();
}
