//! Kiro, its IDE and CLI alike: `settings/mcp.json` in `$KIRO_HOME`, else
//! `~/.kiro`, servers under `mcpServers`.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Milliseconds Kiro waits for one request, written into the entry, for
/// the first analysis of a large binary.
const TIMEOUT_MS: u32 = 600_000;

/// A Kiro server entry.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
    /// Whether it is turned off.
    disabled: bool,
    /// Milliseconds one request may take.
    timeout: u32,
}

/// Kiro.
#[derive(Debug)]
pub(super) struct Kiro;

impl Client for Kiro {
    fn name(&self) -> &'static str {
        "kiro"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env.var("KIRO_HOME").or_else(|| env.home(".kiro"))?;
        let file = dir.join("settings").join("mcp.json");
        Some((dir, file))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            command,
            args: [],
            disabled: false,
            timeout: TIMEOUT_MS,
        })
    }
}
