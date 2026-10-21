//! Augment's Auggie CLI: `~/.augment/settings.json`, servers under
//! `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Augment.
#[derive(Debug)]
pub(super) struct Auggie;

impl Client for Auggie {
    fn name(&self) -> &'static str {
        "augment"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(env.home(".augment"), "settings.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
