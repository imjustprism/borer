//! Windsurf: `~/.codeium/windsurf/mcp_config.json`, servers under
//! `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Windsurf.
#[derive(Debug)]
pub(super) struct Windsurf;

impl Client for Windsurf {
    fn name(&self) -> &'static str {
        "windsurf"
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let _ = os;
        at(env.home(".codeium/windsurf"), "mcp_config.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
