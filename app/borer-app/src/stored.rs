//! What the app keeps between runs in Zed's key-value store under the app's data directory.
//!
//! That is where a load looks for a binary's PDB and packs and the actions that change it,
//! the binaries opened last ([`crate::recent`]), and the code tabs open at quit.
//!
//! These live in the key-value store, not the settings file: Zed's settings schema at this
//! pin is a closed struct whose parser drops every key it does not name, so an app key there
//! would never read back.

use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Context as _;
use borer_front::places;
use db::kvp::KeyValueStore;
use gpui::{
    App, AppContext as _, Context, Entity, Global, PathPromptOptions, Task, WeakEntity, Window,
};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use workspace::Workspace;

use crate::actions::{ChoosePacks, ChooseSymbolCache, ForgetPacks, ForgetSymbolCache};
use crate::binary::Binary;
use crate::commands;
use crate::decompile_item::{DecompileItem, TabMode};
use crate::places::{Opening, Place, place_of};
use crate::shell::Shell;
use crate::worker::{LoadedBinary, Sources};

/// Namespace of the app's keys in Zed's key-value store.
pub(crate) const SCOPE: &str = "borer";

/// A record the app keeps in [`SCOPE`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Key {
    /// The [`OpenSettings`].
    Open,
    /// The [`SavedTab`]s.
    Tabs,
    /// The binaries opened last, with what the engine said each is ([`crate::recent`]).
    RecentBinaries,
}

impl Key {
    /// Returns the key's name in the store.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Open => "open",
            Self::Tabs => "tabs",
            Self::RecentBinaries => "recent_binaries",
        }
    }
}

/// A code tab open at quit, which the next start opens again when its binary is still the
/// same file.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SavedTab {
    /// The binary the tab's function belongs to.
    pub path: PathBuf,
    /// The binary's SHA-256 when the tab was saved, as a project file records it.
    pub sha256: String,
    /// What the tab shows.
    pub place: Place,
    /// Zero-based index of the line at the top of the tab.
    pub top: usize,
}

/// Returns what the key-value store holds under `key`, the type's default when nothing.
///
/// # Arguments
///
/// * `key` - The record.
/// * `cx` - Application context reading the store.
///
/// # Errors
///
/// Returns an error when the store cannot be read or what it holds does not parse.
pub fn read<T: DeserializeOwned + Default>(key: Key, cx: &App) -> anyhow::Result<T> {
    let name = key.name();
    parse(name, KeyValueStore::global(cx).scoped(SCOPE).read(name)?)
}

/// Returns what `text`, the store's record under `key`, holds; the type's default when
/// there is none.
///
/// # Arguments
///
/// * `key` - The key the record is under, for the error.
/// * `text` - The record, `None` when there is none.
///
/// # Errors
///
/// Returns an error when the record does not parse.
fn parse<T: DeserializeOwned + Default>(key: &str, text: Option<String>) -> anyhow::Result<T> {
    let Some(text) = text else {
        return Ok(T::default());
    };
    serde_json::from_str(&text).with_context(|| format!("parsing the app's {key} record"))
}

/// Writes `value` to the key-value store under `key`.
///
/// # Arguments
///
/// * `key` - The record.
/// * `value` - What to keep.
/// * `cx` - Application context.
///
/// # Returns
///
/// The write, which fails when the store refuses it or `value` does not serialize.
pub fn write<T: Serialize>(key: Key, value: &T, cx: &App) -> Task<anyhow::Result<()>> {
    let kvp = KeyValueStore::global(cx);
    let text = serde_json::to_string(value);
    let name = key.name();
    cx.background_spawn(async move { kvp.scoped(SCOPE).write(name.to_owned(), text?).await })
}

/// Returns the code tabs open at the last quit, in tab order.
///
/// # Arguments
///
/// * `cx` - Application context reading the store.
///
/// # Errors
///
/// Returns an error when the store cannot be read or what it holds does not parse.
pub fn saved_tabs(cx: &App) -> anyhow::Result<Vec<SavedTab>> {
    read(Key::Tabs, cx)
}

/// Keeps `tabs` as the code tabs open now, in place of those kept before.
///
/// # Arguments
///
/// * `tabs` - The tabs, in tab order.
/// * `cx` - Application context.
///
/// # Returns
///
/// The write, which fails when the store refuses it.
pub fn keep_tabs(tabs: &[SavedTab], cx: &App) -> Task<anyhow::Result<()>> {
    write(Key::Tabs, &tabs, cx)
}

/// What the person set for opening binaries; what is unset falls back to
/// [`default_sources`].
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpenSettings {
    /// Root of the symbol-server cache a binary's PDB is looked for in, `None` for the
    /// default one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub symbol_cache: Option<PathBuf>,
    /// Pack files that load for every binary, in load order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub packs: Vec<PathBuf>,
}

/// Which open setting an action changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Choice {
    /// The symbol cache directory.
    SymbolCache,
    /// The pack files.
    Packs,
}

/// Sources every load uses in place of the ones the person set, for tests and measurement
/// runs, so they read no packs or symbol cache of the machine's.
#[derive(Debug, Clone, Default)]
pub struct FixedSources(pub Sources);

impl Global for FixedSources {}

/// Returns where a load looks when the person set nothing, as the server does by default.
///
/// That is [`borer_front::places`]' symbol cache and, unless `BORER_AUTO_PACKS=0`, its pack
/// directories, and a note when the symbol cache is refused.
#[must_use]
pub fn default_sources() -> (Sources, Vec<String>) {
    let (symbol_cache, notes) = match places::symbol_cache() {
        Ok(dir) => (dir, Vec::new()),
        Err(why) => (None, vec![format!("skipped the symbol cache: {why}")]),
    };
    let sources = Sources {
        symbol_cache,
        packs: Vec::new(),
        pack_dirs: places::searched(places::auto_enabled()),
    };
    (sources, notes)
}

/// Returns the open settings the key-value store holds.
///
/// # Arguments
///
/// * `cx` - Application context reading the store.
///
/// # Errors
///
/// Returns an error when the store cannot be read or what it holds does not parse.
pub fn open_settings(cx: &App) -> anyhow::Result<OpenSettings> {
    read(Key::Open, cx)
}

/// Returns where the next load looks: [`FixedSources`] when set, else [`default_sources`]
/// with what the person set over it ([`merged`]), and the notes on them.
///
/// # Arguments
///
/// * `cx` - Application context reading the store.
#[must_use]
pub fn sources(cx: &App) -> (Sources, Vec<String>) {
    if let Some(fixed) = cx.try_global::<FixedSources>() {
        return (fixed.0.clone(), Vec::new());
    }
    merged(default_sources(), open_settings(cx))
}

/// Returns `defaults` with the person's `settings` over them: their symbol cache when they
/// set one, and their pack files; settings that do not read leave the defaults and a note.
///
/// # Arguments
///
/// * `(sources, notes)` - The defaults and their notes ([`default_sources`]).
/// * `settings` - The person's settings, or why they do not read.
#[must_use]
pub fn merged(
    (mut sources, mut notes): (Sources, Vec<String>),
    settings: anyhow::Result<OpenSettings>,
) -> (Sources, Vec<String>) {
    match settings {
        Ok(settings) => {
            if settings.symbol_cache.is_some() {
                sources.symbol_cache = settings.symbol_cache;
            }
            sources.packs = settings.packs;
        }
        Err(err) => notes.push(format!("open settings left out: {err:#}")),
    }
    (sources, notes)
}

/// Says what `paths` are, one after another.
///
/// # Arguments
///
/// * `paths` - The paths.
fn listed(paths: &[PathBuf]) -> String {
    paths
        .iter()
        .map(|p| p.display().to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

/// Changes one open setting with `change`, saves it, and says on `binary`'s status line what
/// it is now, which the next open uses.
///
/// # Arguments
///
/// * `binary` - The binary whose status line takes the answer.
/// * `change` - Changes the settings and says what they hold now.
/// * `cx` - Binary context.
fn update(
    binary: &mut Binary,
    change: impl FnOnce(&mut OpenSettings) -> String,
    cx: &mut Context<'_, Binary>,
) {
    let mut settings = match open_settings(cx) {
        Ok(settings) => settings,
        Err(err) => {
            binary.set_status(format!("open settings not changed: {err:#}"), cx);
            return;
        }
    };
    let said = change(&mut settings);
    let saving = write(Key::Open, &settings, cx);
    cx.spawn(async move |this, cx| {
        let status = match saving.await {
            Ok(()) => format!("{said}; the next open uses it"),
            Err(err) => format!("open settings not saved: {err:#}"),
        };
        if let Some(this) = this.upgrade() {
            this.update(cx, |binary, cx| binary.set_status(status, cx));
        }
    })
    .detach();
}

/// Asks for the symbol cache directory or the pack files through the system dialog and
/// keeps what the person picks; a cancelled dialog changes nothing.
///
/// # Arguments
///
/// * `what` - The setting to choose.
/// * `binary` - The binary whose status line says what changed.
/// * `cx` - Application context.
pub fn choose(what: Choice, binary: &Entity<Binary>, cx: &mut App) {
    let packs = what == Choice::Packs;
    let options = PathPromptOptions {
        files: packs,
        directories: !packs,
        multiple: packs,
        prompt: None,
    };
    binary.update(cx, |binary, cx| {
        binary.pick(
            options,
            move |binary, picked, cx| {
                update(
                    binary,
                    move |settings| match what {
                        Choice::SymbolCache => {
                            let dir = picked.into_iter().next().unwrap_or_default();
                            let said = format!("symbol cache {}", dir.display());
                            settings.symbol_cache = Some(dir);
                            said
                        }
                        Choice::Packs => {
                            let said = format!("packs {}", listed(&picked));
                            settings.packs = picked;
                            said
                        }
                    },
                    cx,
                );
            },
            cx,
        );
    });
}

/// Puts one open setting back to what [`default_sources`] says.
///
/// # Arguments
///
/// * `what` - The setting to forget.
/// * `binary` - The binary whose status line says what changed.
/// * `cx` - Application context.
pub fn forget(what: Choice, binary: &Entity<Binary>, cx: &mut App) {
    binary.update(cx, |binary, cx| {
        update(
            binary,
            |settings| match what {
                Choice::SymbolCache => {
                    settings.symbol_cache = None;
                    default_sources().0.symbol_cache.map_or_else(
                        || "no symbol cache".to_owned(),
                        |dir| format!("symbol cache {}", dir.display()),
                    )
                }
                Choice::Packs => {
                    settings.packs.clear();
                    "no pack files".to_owned()
                }
            },
            cx,
        );
    });
}

/// Registers the actions that change the open settings on `workspace`, each on `binary`.
///
/// # Arguments
///
/// * `workspace` - The workspace the actions dispatch in.
/// * `binary` - The window's binary, whose status line says what changed.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let on = |what: Choice, change: fn(Choice, &Entity<Binary>, &mut App)| {
        let binary = binary.clone();
        move |_: &mut Workspace, cx: &mut App| change(what, &binary, cx)
    };
    let (cache, packs) = (on(Choice::SymbolCache, choose), on(Choice::Packs, choose));
    let (no_cache, no_packs) = (on(Choice::SymbolCache, forget), on(Choice::Packs, forget));
    commands::register(workspace, binary, move |w, _: &ChooseSymbolCache, _, cx| {
        cache(w, cx);
    });
    commands::register(workspace, binary, move |w, _: &ChoosePacks, _, cx| {
        packs(w, cx);
    });
    commands::register(workspace, binary, move |w, _: &ForgetSymbolCache, _, cx| {
        no_cache(w, cx);
    });
    commands::register(workspace, binary, move |w, _: &ForgetPacks, _, cx| {
        no_packs(w, cx);
    });
}

/// Returns the write of every app window's open code tabs to the store, which the next
/// start restores ([`Binary::restore`]).
///
/// It runs on quit, and as a window closes, before it goes; with no app window left it
/// writes nothing, so the tabs the last window kept as it closed stay. A write that fails
/// is said on stderr.
///
/// # Arguments
///
/// * `cx` - Application context listing the windows.
pub(crate) fn keep_open_tabs(cx: &mut App) -> impl Future<Output = ()> + use<> {
    let app: &App = cx;
    let tabs: Vec<SavedTab> = app
        .windows()
        .into_iter()
        .filter_map(|window| window.downcast::<Shell>())
        .filter_map(|window| window.read(app).ok())
        .flat_map(|shell| open_tabs(shell.workspace().read(app), app))
        .collect();
    let keep = keep_tabs(&tabs, cx);
    async move {
        if let Err(err) = keep.await {
            eprintln!("borer-app: open tabs not kept: {err:#}");
        }
    }
}

/// Returns the code tabs of `workspace`'s panes that show a function, by place, in tab order.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `cx` - Application context reading the tabs.
pub(crate) fn open_tabs(workspace: &Workspace, cx: &App) -> Vec<SavedTab> {
    workspace
        .panes()
        .iter()
        .flat_map(|pane| pane.read(cx).items_of_type::<DecompileItem>())
        .filter_map(|item| {
            let place = place_of(&item, cx)?;
            let item = item.read(cx);
            Some(SavedTab {
                path: item.loaded().path.clone(),
                sha256: item.loaded().identity.clone(),
                place,
                top: item.top_line(),
            })
        })
        .collect()
}

/// Opens the places a restore found unchanged in `loaded`, each at its top line.
///
/// Each is a permanent tab, the last one active; it runs once the load's other followers
/// ran, so the first function the panel docked with opens behind them. The panel opens
/// that function on a deferred update of its own, so the restore is deferred twice.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary, holding the places ([`Binary::take_restored`]).
/// * `loaded` - The binary the restore opened.
/// * `window` - Window the workspace is in.
/// * `cx` - Application context.
pub(crate) fn restore_places(
    workspace: &WeakEntity<Workspace>,
    binary: &Entity<Binary>,
    loaded: &Arc<LoadedBinary>,
    window: &mut Window,
    cx: &mut App,
) {
    let restored = binary.update(cx, |binary, _| binary.take_restored());
    let Some(workspace) = workspace.upgrade().filter(|_| !restored.is_empty()) else {
        return;
    };
    workspace.update(cx, |workspace, cx| {
        for (place, top) in restored {
            let how = Opening {
                mode: TabMode::Permanent,
                focus: true,
            };
            crate::places::open(workspace, binary, loaded, place, how, window, cx);
            if let Some(item) = workspace.active_item_as::<DecompileItem>(cx) {
                item.update(cx, |item, _| item.restore_top(top));
            }
        }
    });
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{OpenSettings, merged};
    use crate::worker::Sources;

    /// The person's symbol cache and pack files go over the defaults, an unset cache keeps
    /// the default one, and settings that do not read leave the defaults with a note after
    /// theirs.
    ///
    /// # Panics
    ///
    /// Panics if a merge keeps the wrong value or says the wrong notes.
    #[test]
    fn the_persons_settings_go_over_the_defaults() {
        let defaults = Sources {
            symbol_cache: Some(PathBuf::from("cache")),
            packs: Vec::new(),
            pack_dirs: vec![PathBuf::from("dir")],
        };
        let set = OpenSettings {
            symbol_cache: Some(PathBuf::from("mine")),
            packs: vec![PathBuf::from("a.borer")],
        };
        let (sources, notes) = merged((defaults.clone(), Vec::new()), Ok(set));
        let want = Sources {
            symbol_cache: Some(PathBuf::from("mine")),
            packs: vec![PathBuf::from("a.borer")],
            pack_dirs: vec![PathBuf::from("dir")],
        };
        assert_eq!((sources, notes), (want, Vec::new()));
        let unset = merged((defaults.clone(), Vec::new()), Ok(OpenSettings::default()));
        assert_eq!(unset, (defaults.clone(), Vec::new()));
        let noted = vec!["skipped the symbol cache: a share".to_owned()];
        let (sources, notes) = merged((defaults.clone(), noted), Err(anyhow::anyhow!("bad json")));
        assert_eq!(sources, defaults);
        assert_eq!(
            notes,
            [
                "skipped the symbol cache: a share",
                "open settings left out: bad json"
            ]
        );
    }
}
