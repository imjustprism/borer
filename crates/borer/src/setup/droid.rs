//! Factory Droid: `~/.factory/mcp.json`, servers under `mcpServers` with
//! their transport stated.

use std::path::PathBuf;

use super::client::{Client, Format, TypedStdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Factory droid.
#[derive(Debug)]
pub(super) struct Droid;

impl Client for Droid {
    fn name(&self) -> &'static str {
        "factory droid"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(env.home(".factory"), "mcp.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&TypedStdio::new(command))
    }
}
