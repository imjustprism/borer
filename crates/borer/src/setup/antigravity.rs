//! Google Antigravity: `~/.gemini/config/mcp_config.json`, servers under
//! `mcpServers`; installed when `~/.gemini/antigravity` is there.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Antigravity.
#[derive(Debug)]
pub(super) struct Antigravity;

impl Client for Antigravity {
    fn name(&self) -> &'static str {
        "antigravity"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env.home(".gemini/antigravity")?;
        let file = env.home(".gemini/config/mcp_config.json")?;
        Some((dir, file))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
