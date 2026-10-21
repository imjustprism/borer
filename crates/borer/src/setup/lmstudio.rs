//! LM Studio: `mcp.json` in its home, which is the folder
//! `~/.lmstudio-home-pointer` names, else `~/.cache/lm-studio` when it is
//! there, else `~/.lmstudio`; servers under `mcpServers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Lm studio.
#[derive(Debug)]
pub(super) struct LmStudio;

impl Client for LmStudio {
    fn name(&self) -> &'static str {
        "lm studio"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let pointer = env.home(".lmstudio-home-pointer")?;
        let named = std::fs::read_to_string(&pointer)
            .ok()
            .map(|t| PathBuf::from(t.trim()))
            .filter(|p| !p.as_os_str().is_empty());
        let cache = env.home(".cache/lm-studio").filter(|d| d.is_dir());
        at(
            named.or(cache).or_else(|| env.home(".lmstudio")),
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
