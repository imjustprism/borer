//! Grok Build, xAI's CLI: a `[mcp_servers.borer]` table in `config.toml`
//! under `$GROK_HOME`, else `~/.grok`.
//!
//! The community grok-cli keeps its own
//! `user-settings.json` in the same folder; a folder holding only that is
//! not Grok Build's.

use std::path::PathBuf;

use super::client::{Client, Format, at};
use super::env::{Env, Os};
use super::toml::toml_string;

/// Grok Build.
#[derive(Debug)]
pub(super) struct Grok;

impl Client for Grok {
    fn name(&self) -> &'static str {
        "grok build"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env
            .var("GROK_HOME")
            .filter(|d| borer_engine::program::unusable_path(d).is_none())
            .or_else(|| env.home(".grok"))?;
        let is_file = |name: &str| {
            matches!(
                borer_engine::program::checked_metadata(&dir.join(name)),
                Ok(Some(m)) if m.is_file()
            )
        };
        if is_file("user-settings.json") && !is_file("config.toml") {
            return None;
        }
        at(Some(dir), "config.toml")
    }

    fn format(&self) -> Format {
        Format::Toml
    }

    fn entry(&self, command: &str) -> String {
        format!("command = {}\nargs = []", toml_string(command))
    }
}
