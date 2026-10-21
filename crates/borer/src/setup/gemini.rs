//! Gemini CLI: `~/.gemini/settings.json`, servers under `mcpServers`.
//! Antigravity writes under `~/.gemini` too, so a folder holding only its
//! files is not Gemini CLI's.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio};
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
        let dir = env.home(".gemini")?;
        let settings = dir.join("settings.json");
        if !settings.is_file() && dir.join("antigravity").is_dir() {
            return None;
        }
        Some((dir, settings))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
