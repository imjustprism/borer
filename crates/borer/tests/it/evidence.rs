//! The evidence line over JSON-RPC stdio on the real binary
//! (`CARGO_BIN_EXE_borer`): every tool answer carries one naming it, the
//! id returns the text behind it, and past the cap the oldest is let go.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
#![expect(
    clippy::panic,
    reason = "a server that cannot be driven has no useful recovery in a test client"
)]

use crate::contract::tiny_pe;
use crate::reload::Client;
use crate::resources::read;

/// The evidence id an answer's last line names.
///
/// # Arguments
///
/// * `answer` - A tool answer as sent.
///
/// # Returns
///
/// The id after `# evidence: `.
///
/// # Panics
///
/// When the answer does not end with a well-formed evidence line.
fn evidence_id(answer: &str) -> String {
    let id = answer
        .lines()
        .last()
        .and_then(|l| l.strip_prefix("# evidence: "))
        .unwrap_or_else(|| panic!("no evidence line ends it: {answer}"));
    let (counter, digest) = id
        .split_once('-')
        .unwrap_or_else(|| panic!("not <n>-<digest>: {id}"));
    assert!(
        !counter.is_empty() && counter.chars().all(|c| c.is_ascii_alphanumeric()),
        "{id}"
    );
    assert_eq!(digest.len(), 8, "{id}");
    assert!(digest.chars().all(|c| c.is_ascii_hexdigit()), "{id}");
    id.to_owned()
}

/// Every tool answer ends with an evidence line naming it, the id returns
/// the answer exactly as it was sent, and past the 256 the session keeps
/// the oldest is let go and its id says so.
#[test]
fn every_answer_carries_evidence_that_returns_it_and_lets_the_oldest_go() {
    /// One more than the answers the session keeps, to push the first out.
    const PAST_THE_CAP: usize = 257;
    let file = std::env::temp_dir().join(format!("borer_evidence_{}.exe", std::process::id()));
    std::fs::write(&file, tiny_pe()).expect("the fixture is writable");
    let mut client = Client::start(&file.to_string_lossy());
    let first = client.text("binary_info", "{}");
    let first_id = evidence_id(&first);
    let back =
        read(&mut client, &format!("borer://session/evidence/{first_id}")).expect("the id answers");
    assert_eq!(back, first, "the id returns the answer as it was sent");
    let again = client.text("binary_info", "{}");
    let again_id = evidence_id(&again);
    assert_ne!(again_id, first_id, "the counter names the emission");
    assert_eq!(
        again_id.split_once('-').map(|(_, digest)| digest),
        first_id.split_once('-').map(|(_, digest)| digest),
        "the digest names the text, and the text did not change"
    );
    for _ in 0..PAST_THE_CAP {
        assert!(client.text("binary_info", "{}").contains("# evidence: "));
    }
    let let_go = read(&mut client, &format!("borer://session/evidence/{first_id}"))
        .expect("an id let go answers a notice");
    assert!(let_go.contains("was let go"), "{let_go}");
    let last = client.text("binary_info", "{}");
    let last_id = evidence_id(&last);
    let kept = read(&mut client, &format!("borer://session/evidence/{last_id}"))
        .expect("the newest answers");
    assert_eq!(kept, last);
    let refused = read(&mut client, "borer://session/evidence/zzzz-00000000")
        .expect_err("an id the session never minted");
    assert!(refused.contains("names no answer"), "{refused}");
    client.finish();
    std::fs::remove_file(&file).ok();
}
