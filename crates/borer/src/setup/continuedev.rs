//! Continue: a file of its own, `~/.continue/mcpServers/borer.json` (or
//! under `$CONTINUE_GLOBAL_DIR`), in the `mcpServers` form Continue reads
//! beside its YAML blocks.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Continue.
#[derive(Debug)]
pub(super) struct Continue;

impl Client for Continue {
    fn name(&self) -> &'static str {
        "continue"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env
            .var("CONTINUE_GLOBAL_DIR")
            .or_else(|| env.home(".continue"))?;
        let file = dir.join("mcpServers").join("borer.json");
        Some((dir, file))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
