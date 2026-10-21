//! Junie, `JetBrains`' agent: `~/.junie/mcp/mcp.json`, shared by its IDE
//! plugin and CLI, servers under `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Junie.
#[derive(Debug)]
pub(super) struct Junie;

impl Client for Junie {
    fn name(&self) -> &'static str {
        "junie"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env.home(".junie")?;
        let file = dir.join("mcp").join("mcp.json");
        Some((dir, file))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
