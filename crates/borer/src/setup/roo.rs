//! Roo Code: `settings/mcp_settings.json` in its VS Code global storage,
//! servers under `mcpServers`.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Seconds Roo Code waits for one request, written into the entry: its
/// default of 60 is less than the first analysis of a large binary takes.
const TIMEOUT_SEC: u32 = 600;

/// A Roo Code server entry.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
    /// Seconds one request may take.
    timeout: u32,
}

/// Roo code.
#[derive(Debug)]
pub(super) struct Roo;

impl Client for Roo {
    fn name(&self) -> &'static str {
        "roo code"
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env.roaming(os, "Code/User/globalStorage/rooveterinaryinc.roo-cline")?;
        let file = dir.join("settings").join("mcp_settings.json");
        Some((dir, file))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            command,
            args: [],
            timeout: TIMEOUT_SEC,
        })
    }
}
