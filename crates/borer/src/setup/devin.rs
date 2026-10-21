//! Devin Desktop: `mcp_config.json` in its configuration directory,
//! servers under `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Devin.
#[derive(Debug)]
pub(super) struct Devin;

impl Client for Devin {
    fn name(&self) -> &'static str {
        "devin desktop"
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(env.config(os, "devin"), "mcp_config.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
