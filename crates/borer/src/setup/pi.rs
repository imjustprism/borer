//! pi: `mcp.json` in its agent directory, `$PI_CODING_AGENT_DIR`, else
//! `~/.pi/agent`, servers under `mcpServers`.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Seconds pi waits for one request, written into the entry: its default
/// of 60 is less than the first analysis of a large binary takes.
const TIMEOUT_SEC: u32 = 600;

/// pi.
#[derive(Debug)]
pub(super) struct Pi;

/// How pi offers a server's tools to the model.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "lowercase")]
enum Exposure {
    /// Declared like built-in tools, rather than reached only from
    /// codemode scripts, pi's default.
    Direct,
}

/// A pi server entry.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
    /// Seconds one request may take.
    timeout: u32,
    /// How the tools reach the model.
    exposure: Exposure,
}

impl Client for Pi {
    fn name(&self) -> &'static str {
        "pi"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(env.pi.clone(), "mcp.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            command,
            args: [],
            timeout: TIMEOUT_SEC,
            exposure: Exposure::Direct,
        })
    }

    fn restart_note(&self) -> &'static str {
        " (or run /reload in a session)"
    }
}

#[cfg(test)]
mod tests {
    use super::super::client::Client as _;
    use super::Pi;

    /// The entry carries the long timeout and direct tools.
    ///
    /// # Panics
    ///
    /// When it differs.
    #[test]
    fn the_entry_waits_long_and_declares_its_tools() {
        assert_eq!(
            Pi.entry("/opt/borer"),
            r#"{"command": "/opt/borer", "args": [], "timeout": 600, "exposure": "direct"}"#
        );
    }
}
