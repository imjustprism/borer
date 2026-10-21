//! Amp: `settings.json` (or a `settings.jsonc` already there) in
//! `~/.config/amp`, on Windows too, servers under `amp.mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, json_or_jsonc};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Amp.
#[derive(Debug)]
pub(super) struct Amp;

impl Client for Amp {
    fn name(&self) -> &'static str {
        "amp"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        json_or_jsonc(env.xdg("amp"), "settings")
    }

    fn format(&self) -> Format {
        Format::Json {
            key: "amp.mcpServers",
        }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
