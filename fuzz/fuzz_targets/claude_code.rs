//! Reads arbitrary bytes as lines Claude Code's command line writes to the app's chat, and
//! each MCP message among them as the app's MCP server would answer it: any line may be
//! refused, none may panic, hang or exhaust memory.

#![no_main]

use borer_front::claude_code::{Event, mcp, read};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };
    for line in text.lines() {
        if let Ok(Event::Mcp { message, .. }) = read(line) {
            _ = mcp(&message);
        }
    }
});
