//! Cursor: `~/.cursor/mcp.json`, servers under `mcpServers` with their
//! transport stated.

use std::path::PathBuf;

use super::client::{Client, Format, TypedStdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Cursor.
#[derive(Debug)]
pub(super) struct Cursor;

impl Client for Cursor {
    fn name(&self) -> &'static str {
        "cursor"
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let _ = os;
        at(env.home(".cursor"), "mcp.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&TypedStdio::new(command))
    }

    fn restart_note(&self) -> &'static str {
        " (then turn borer on under Settings > MCP)"
    }
}
