//! Kimi Code: `mcp.json` in `$KIMI_CODE_HOME`, else `~/.kimi-code`, servers
//! under `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Kimi code.
#[derive(Debug)]
pub(super) struct Kimi;

impl Client for Kimi {
    fn name(&self) -> &'static str {
        "kimi code"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(
            env.var("KIMI_CODE_HOME").or_else(|| env.home(".kimi-code")),
            "mcp.json",
        )
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
