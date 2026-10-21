//! Qwen Code: `settings.json` in `$QWEN_HOME`, else `~/.qwen`, servers
//! under `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Qwen code.
#[derive(Debug)]
pub(super) struct Qwen;

impl Client for Qwen {
    fn name(&self) -> &'static str {
        "qwen code"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(
            env.var("QWEN_HOME").or_else(|| env.home(".qwen")),
            "settings.json",
        )
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
