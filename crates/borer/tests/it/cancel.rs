//! The client's cancel (`notifications/cancelled`), driven over JSON-RPC
//! stdio on the real binary.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::time::{Duration, Instant};

use crate::contract::tiny_pe;
use crate::reload::Client;

/// Requests a session sends and then cancels: each emulates a spin for
/// two seconds or more, two at a time, so run to their end they would hold
/// the permits for many times [`PROMPT`].
const LONG: u64 = 12;

/// Longest a request sent after the cancels may wait for its reply.
const PROMPT: Duration = Duration::from_secs(5);

/// Requests the client cancels stop where the deadline would stop them
/// and answer nothing.
///
/// A request sent after the cancels gets its permit and its reply at
/// once, and no reply to a cancelled one arrives first. Half the requests
/// are tool calls and half resource reads, so both routes carry the
/// client's cancel.
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "how soon the reply comes is what the test measures"
)]
fn cancelled_requests_stop_and_answer_nothing() {
    let file = std::env::temp_dir().join(format!("borer_cancel_{}.exe", std::process::id()));
    let mut pe = tiny_pe();
    pe.splice(0x200..0x202, [0xeb, 0xfe]); // ASM: jmp $
    std::fs::write(&file, pe).expect("the fixture is writable");
    let mut client = Client::start(&file.to_string_lossy());
    let ids = 1000..1000 + LONG;
    let requests: Vec<String> = ids
        .clone()
        .map(|id| {
            let uri = format!("borer://emulate/0x140001000,steps={}", 20_000_000 - id);
            if id % 2 == 0 {
                format!(
                    r#"{{"jsonrpc":"2.0","id":{id},"method":"tools/call","params":{{"name":"query","arguments":{{"uri":"{uri}"}}}}}}"#
                )
            } else {
                format!(
                    r#"{{"jsonrpc":"2.0","id":{id},"method":"resources/read","params":{{"uri":"{uri}"}}}}"#
                )
            }
        })
        .collect();
    client.write(&requests.join("\n"));
    let cancels: Vec<String> = ids
        .clone()
        .map(|id| {
            format!(
                r#"{{"jsonrpc":"2.0","method":"notifications/cancelled","params":{{"requestId":{id},"reason":"the test moved on"}}}}"#
            )
        })
        .collect();
    client.write(&cancels.join("\n"));
    let asked = Instant::now();
    let info = client.text("binary_info", "{}");
    let took = asked.elapsed();
    assert!(info.contains("PE"), "{info}");
    assert!(took < PROMPT, "the reply after the cancels took {took:?}");
    for id in ids {
        let tag = format!("\"id\":{id},");
        assert!(
            client.passed.iter().all(|line| !line.contains(&tag)),
            "a cancelled request answered: {:?}",
            client.passed
        );
    }
    client.finish();
    std::fs::remove_file(&file).expect("the fixture is removable");
}
