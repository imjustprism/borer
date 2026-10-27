//! What each tool touches beyond the program it reads, and the manifest
//! `borer tools` prints from it.
//!
//! The four MCP annotation hints say whether a tool writes and whether it
//! reaches past the server; a guard deciding what to allow also needs to
//! know what it writes and where it reaches. Each tool states that on its
//! own definition, as [`Effect`]s under [`EFFECTS_KEY`] in its `_meta`,
//! so a tool and its facts change together. `tools/list` leaves them out
//! (every agent would pay for them in its context); [`manifest`] lists
//! them with the hints, the one source every guard or registry entry is
//! generated from (`scripts/dev/tool_safety.py`).

use rmcp::model::{JsonObject, MetaObject, Tool};

/// The `_meta` key a tool's definition keeps its effects under.
pub(crate) const EFFECTS_KEY: &str = "lol.borer/effects";

/// The manifest's schema id; a change of its shape changes the version.
const SCHEMA: &str = "borer.tool-safety.v1";

/// Something a tool touches outside the loaded program and its analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Effect {
    /// Reads a file at a path the caller names.
    ReadsFiles,
    /// Writes a file: under the output root, or the symbol cache.
    WritesFiles,
    /// Connects to a server over the network.
    Network,
    /// Reads the memory of another running process, never writing it.
    ReadsProcessMemory,
    /// Changes the session: its names, comments, types, loaded program or attach.
    ChangesSession,
    /// Replaces the server process with the borer binary now on disk.
    RestartsServer,
}

impl Effect {
    /// Every effect, in the manifest's order.
    const ALL: [Self; 6] = [
        Self::ReadsFiles,
        Self::WritesFiles,
        Self::Network,
        Self::ReadsProcessMemory,
        Self::ChangesSession,
        Self::RestartsServer,
    ];

    /// Returns the effect's word in `_meta` and the manifest.
    const fn word(self) -> &'static str {
        match self {
            Self::ReadsFiles => "reads-files",
            Self::WritesFiles => "writes-files",
            Self::Network => "network",
            Self::ReadsProcessMemory => "reads-process-memory",
            Self::ChangesSession => "changes-session",
            Self::RestartsServer => "restarts-server",
        }
    }

    /// Returns the effect's meaning, for the manifest's legend.
    const fn meaning(self) -> &'static str {
        match self {
            Self::ReadsFiles => "reads a file at a path the caller names",
            Self::WritesFiles => "writes a file under the output root or into the symbol cache",
            Self::Network => "connects to a server over the network (https only)",
            Self::ReadsProcessMemory => {
                "reads the memory of another running process (Windows), never writing it"
            }
            Self::ChangesSession => {
                "changes the session in memory: names, comments, types, the loaded program or the attach; never the binary"
            }
            Self::RestartsServer => "replaces the server process with the borer binary now on disk",
        }
    }
}

/// Returns the `_meta` a tool's definition carries its effects in.
///
/// # Arguments
///
/// * `list` - What the tool touches; empty for one that only reads the program.
pub(crate) fn effects(list: &[Effect]) -> MetaObject {
    let words = list.iter().map(|e| e.word().into()).collect();
    let mut meta = JsonObject::new();
    meta.insert(EFFECTS_KEY.to_owned(), serde_json::Value::Array(words));
    MetaObject::from(meta)
}

/// Returns the effect words a tool's definition states, none when it states none.
///
/// # Arguments
///
/// * `tool` - The tool as its router defines it.
fn words(tool: &Tool) -> serde_json::Value {
    tool.meta
        .as_ref()
        .and_then(|m| m.get(EFFECTS_KEY))
        .cloned()
        .unwrap_or_else(|| serde_json::Value::Array(Vec::new()))
}

/// Returns the manifest: every tool's name, its four annotation hints and
/// its effects, with a legend of the effect words, as indented JSON.
///
/// # Arguments
///
/// * `tools` - The tools as their router defines them, before
///   `tools/list` slims them.
///
/// # Errors
///
/// When the JSON cannot be written, which a well-formed tool never causes.
pub(crate) fn manifest(tools: &[Tool]) -> serde_json::Result<String> {
    let legend: serde_json::Map<_, _> = Effect::ALL
        .iter()
        .map(|e| (e.word().to_owned(), e.meaning().into()))
        .collect();
    let rows = tools
        .iter()
        .map(|t| {
            Ok(serde_json::json!({
                "name": t.name,
                "annotations": serde_json::to_value(&t.annotations)?,
                "effects": words(t),
            }))
        })
        .collect::<serde_json::Result<Vec<_>>>()?;
    serde_json::to_string_pretty(&serde_json::json!({
        "schema": SCHEMA,
        "server": {"name": "borer", "version": crate::doctor::version()},
        "effects": legend,
        "tools": rows,
    }))
}

#[cfg(test)]
mod tests {
    use super::{Effect, words};

    /// Every tool states all four hints and its effects agree with them.
    ///
    /// A tool writes exactly when it changes the session, writes a file or
    /// restarts the server, and reaches past the server exactly when it
    /// uses the network or another process. The tools a guard holds back
    /// are named, so a new one that writes a file, uses the network or
    /// reads a process fails here until it is added, and then the guard
    /// entries are generated again (`scripts/dev/tool_safety.py`).
    ///
    /// # Panics
    ///
    /// When a tool lacks a hint, its effects contradict its hints, the
    /// named tools differ, or `tools/list` would carry the effects.
    #[test]
    fn every_tool_states_hints_its_effects_agree_with() {
        let tools = crate::BorerServer::tool_router().list_all();
        let named = |e: Effect| -> Vec<&str> {
            tools
                .iter()
                .filter(|t| {
                    words(t)
                        .as_array()
                        .is_some_and(|w| w.contains(&e.word().into()))
                })
                .map(|t| t.name.as_ref())
                .collect()
        };
        for t in &tools {
            let h = t.annotations.clone().unwrap_or_default();
            let (Some(read_only), Some(_), Some(_), Some(open_world)) = (
                h.read_only_hint,
                h.destructive_hint,
                h.idempotent_hint,
                h.open_world_hint,
            ) else {
                panic!("{} does not state all four hints", t.name);
            };
            let has = |e: Effect| named(e).contains(&t.name.as_ref());
            let writes = has(Effect::WritesFiles)
                || has(Effect::ChangesSession)
                || has(Effect::RestartsServer);
            assert_eq!(
                read_only, !writes,
                "{}: readOnlyHint against its effects",
                t.name
            );
            let reaches = has(Effect::Network) || has(Effect::ReadsProcessMemory);
            assert_eq!(
                open_world, reaches,
                "{}: openWorldHint against its effects",
                t.name
            );
            assert!(
                crate::slim_tool(t.clone()).meta.is_none(),
                "{} lists its _meta",
                t.name
            );
        }
        assert_eq!(
            named(Effect::WritesFiles),
            ["decompile_batch", "fetch_pdb", "save_project"]
        );
        assert_eq!(named(Effect::Network), ["fetch_pdb"]);
        let live: &[&str] = if cfg!(windows) {
            &[
                "live_attach",
                "live_instances",
                "live_modules",
                "live_object",
                "live_path",
                "live_read",
                "live_scan",
                "live_watch",
            ]
        } else {
            &[]
        };
        assert_eq!(named(Effect::ReadsProcessMemory), live);
        assert_eq!(named(Effect::RestartsServer), ["reload"]);
    }

    /// The manifest lists every tool once, in name order, with its hints
    /// and effects, and a legend naming every effect word.
    ///
    /// # Panics
    ///
    /// When the manifest does not parse or a tool or word is missing.
    #[test]
    fn the_manifest_lists_every_tool_with_its_facts() {
        let tools = crate::BorerServer::tool_router().list_all();
        let text = super::manifest(&tools).expect("written");
        let doc: serde_json::Value = serde_json::from_str(&text).expect("parses");
        let rows = doc["tools"].as_array().expect("tools");
        assert_eq!(rows.len(), tools.len());
        let save = rows
            .iter()
            .find(|r| r["name"] == "save_project")
            .expect("listed");
        assert_eq!(save["annotations"]["readOnlyHint"], false);
        assert_eq!(save["effects"], serde_json::json!(["writes-files"]));
        for e in Effect::ALL {
            assert!(
                doc["effects"][e.word()].is_string(),
                "{} has no meaning",
                e.word()
            );
        }
    }
}
