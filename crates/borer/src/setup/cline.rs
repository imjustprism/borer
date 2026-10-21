//! Cline: its VS Code extension, CLI and `JetBrains` plugin alike.
//!
//! The file is `~/.cline/data/settings/cline_mcp_settings.json` (or where
//! `$CLINE_MCP_SETTINGS_PATH`, `$CLINE_DATA_DIR` or `$CLINE_DIR` puts it),
//! servers under `mcpServers`.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format, Transport};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Seconds Cline waits for one request, written into the entry: its default
/// of 60 is less than the first analysis of a large binary takes.
const TIMEOUT_SEC: u32 = 600;

/// A Cline server entry. The transport is stated: Cline reads an entry
/// without one as the old SSE kind.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// How it is reached.
    #[serde(rename = "type")]
    transport: Transport,
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
    /// Whether it is turned off.
    disabled: bool,
    /// Tools run without asking: none.
    #[serde(rename = "autoApprove")]
    auto_approve: [&'a str; 0],
    /// Seconds one request may take.
    timeout: u32,
}

/// Cline.
#[derive(Debug)]
pub(super) struct Cline;

impl Client for Cline {
    fn name(&self) -> &'static str {
        "cline"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env.var("CLINE_DIR").or_else(|| env.home(".cline"))?;
        let file = env.var("CLINE_MCP_SETTINGS_PATH").unwrap_or_else(|| {
            env.var("CLINE_DATA_DIR")
                .unwrap_or_else(|| dir.join("data"))
                .join("settings")
                .join("cline_mcp_settings.json")
        });
        Some((dir, file))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            transport: Transport::Stdio,
            command,
            args: [],
            disabled: false,
            auto_approve: [],
            timeout: TIMEOUT_SEC,
        })
    }
}
