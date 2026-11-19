//! Reads arbitrary bytes as GitHub's latest-release answer, and as a version and a tag, the
//! paths the app's and the CLI's update checks take: any input may be refused, none may
//! panic, hang or exhaust memory.

#![no_main]

use borer_front::release::{Version, judge};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let running = Version {
        major: 0,
        minor: 3,
        patch: 1,
    };
    _ = judge(running, Some((200, data)));
    if let Ok(text) = std::str::from_utf8(data) {
        _ = Version::parse(text);
        _ = Version::parse_tag(text);
    }
});
