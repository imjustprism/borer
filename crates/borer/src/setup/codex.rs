//! Codex CLI: a `[mcp_servers.borer]` table in `config.toml` under
//! `$CODEX_HOME`, else `~/.codex`.

use std::path::PathBuf;

use super::client::{Client, Format, at};
use super::env::{Env, Os};
use super::toml::toml_string;

/// Seconds Codex waits for borer to start, written into its table.
const STARTUP_SEC: u32 = 30;

/// Seconds Codex waits for one tool call, written into its table: its
/// default of 60 is less than the first analysis of a large binary takes.
const TOOL_SEC: u32 = 600;

/// Codex CLI.
#[derive(Debug)]
pub(super) struct Codex;

impl Client for Codex {
    fn name(&self) -> &'static str {
        "codex cli"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(env.codex.clone(), "config.toml")
    }

    fn format(&self) -> Format {
        Format::Toml
    }

    fn entry(&self, command: &str) -> String {
        format!(
            "command = {}\nargs = []\nstartup_timeout_sec = {STARTUP_SEC}\ntool_timeout_sec = {TOOL_SEC}",
            toml_string(command)
        )
    }
}
