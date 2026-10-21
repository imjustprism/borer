//! Gemini CLI: `~/.gemini/settings.json`, servers under `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Gemini.
#[derive(Debug)]
pub(super) struct Gemini;

impl Client for Gemini {
    fn name(&self) -> &'static str {
        "gemini cli"
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let _ = os;
        at(env.home(".gemini"), "settings.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
