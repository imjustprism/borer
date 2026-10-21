//! Warp: `~/.warp/.mcp.json`, servers under `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Warp.
#[derive(Debug)]
pub(super) struct Warp;

impl Client for Warp {
    fn name(&self) -> &'static str {
        "warp"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(env.home(".warp"), ".mcp.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
