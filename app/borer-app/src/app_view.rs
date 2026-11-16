//! The app's window: Zed's [`Workspace`] over an empty local [`Project`], with the functions
//! panel in its left dock and the load status in its status bar.
//!
//! Zed's settings, themes, keymap, command palette and persistence run under the app's own
//! data directory. Nothing signs in, updates, reports telemetry or collaborates:
//! `client::init`, `Project::init` and Zed's auto-update, crash, telemetry and call crates are
//! never started, the client's HTTP is Zed's `BlockedHttpClient`, and Node is unavailable.
//!
//! No path ever becomes a project folder, so no folder's settings, context servers, git or
//! login shell run: `workspace::init` and `editor::init`, which register Zed's open, open
//! files, reload and new file actions, are not started; the app's keymap unbinds their keys;
//! a dropped file reaches a tab, and every pane keeps one ([`keep_filled`]); Zed's add folder
//! action opens a binary instead; AI is off and every folder untrusted.

use std::any::{Any, TypeId};
use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Context as _;
use borer_engine::program::checked_metadata;
use client::{Client, UserStore};
use command_palette_hooks::CommandPaletteFilter;
use db::kvp::KeyValueStore;
use editor::Editor;
use gpui::{
    App, AppContext as _, Bounds, Entity, ExternalPaths, WeakEntity, Window, WindowBounds,
    WindowOptions, px, size,
};
use http_client::{BlockedHttpClient, HttpClientWithUrl};
use language::LanguageRegistry;
use node_runtime::NodeRuntime;
use project::trusted_worktrees::{self, DbTrustedPaths};
use project::{LocalProjectFlags, Project};
use session::{AppSession, Session};
use workspace::dock::DockPosition;
use workspace::{
    AddFolderToProject, AppState, DockStructure, MultiWorkspace, Workspace, WorkspaceId,
    WorkspaceStore,
};

use crate::actions::{FocusFilter, Open, ToggleFunctions};
use crate::binary::{Binary, StatusLine};
use crate::functions_panel::{FunctionsPanel, PANEL_KEY};
use crate::measure::CliMode;
use crate::start_item::keep_filled;

/// Directory of the app's settings, keymap, database and logs under the platform's local
/// data directory, kept apart from an installed Zed's.
const DATA_DIR_NAME: &str = "borer-app";

/// Id of the app's one workspace in its own database, the same on every run, so Zed keys
/// the saved panel sizes the same way each time.
const APP_WORKSPACE_ID: i64 = 1;

/// Zed's key-value key for the dock layout of an empty local workspace (private to
/// `workspace::persistence`, which writes it on every serialization).
const DEFAULT_DOCK_STATE_KEY: &str = "default_dock_state";

/// What the status line ends with when a tab refuses a dropped folder.
pub const REFUSED_FOLDER: &str = "is a folder; drop a binary";

/// Default window width in logical pixels.
const WINDOW_WIDTH_PX: f32 = 1280.0;

/// Default window height in logical pixels.
const WINDOW_HEIGHT_PX: f32 = 800.0;

/// Returns the data directory of a run in `mode`.
///
/// That is `given` when the command line names one, else the app's own under the
/// platform's local data directory for a person. A measurement must be given one, a fresh directory its caller creates and removes, so it
/// neither reads nor writes the person's layout and nothing it leaves outlives the caller.
///
/// # Arguments
///
/// * `mode` - The run's mode.
/// * `given` - The directory `--data-dir` names, if any.
///
/// # Errors
///
/// Returns an error when a measurement names no directory or the platform has no local
/// data directory.
pub fn data_dir(mode: &CliMode, given: Option<PathBuf>) -> anyhow::Result<PathBuf> {
    if let Some(dir) = given {
        return Ok(dir);
    }
    match mode {
        CliMode::Interactive(_) => Ok(dirs::data_local_dir()
            .context("the platform has no local data directory")?
            .join(DATA_DIR_NAME)),
        CliMode::FirstFrame
        | CliMode::ReportOpen(_)
        | CliMode::Headless(_)
        | CliMode::MeasureMemory(_)
        | CliMode::Measure(_)
        | CliMode::MeasureDrop(..) => anyhow::bail!(
            "a measurement run needs --data-dir <dir>, a fresh directory its caller removes"
        ),
    }
}

/// Points Zed's settings, keymap, database and logs at `dir`, and creates the config
/// directory there, which the person's settings file is written in.
///
/// Must run before anything reads Zed's data or config directory.
///
/// # Arguments
///
/// * `dir` - The data directory, from [`data_dir`].
///
/// # Errors
///
/// Returns an error when a directory cannot be created or the path is not UTF-8.
pub fn set_data_dir(dir: &Path) -> anyhow::Result<()> {
    std::fs::create_dir_all(dir).with_context(|| format!("creating {}", dir.display()))?;
    let name = dir
        .to_str()
        .with_context(|| format!("the data directory {} is not UTF-8", dir.display()))?;
    paths::set_custom_data_dir(name);
    let config = paths::config_dir();
    std::fs::create_dir_all(config).with_context(|| format!("creating {}", config.display()))
}

/// Returns the options of a new app window: centered at the default size.
///
/// # Arguments
///
/// * `cx` - Application context reading the displays.
#[must_use]
pub fn window_options(cx: &App) -> WindowOptions {
    let bounds = Bounds::centered(None, size(px(WINDOW_WIDTH_PX), px(WINDOW_HEIGHT_PX)), cx);
    WindowOptions {
        window_bounds: Some(WindowBounds::Windowed(bounds)),
        ..WindowOptions::default()
    }
}

/// Starts Zed's database, settings, themes, fonts, keymap, workspace and command palette
/// for the app, after [`set_data_dir`].
///
/// # Arguments
///
/// * `cx` - Application context.
///
/// # Returns
///
/// The app state every workspace window is built from.
///
/// # Errors
///
/// Returns an error when Zed's fonts do not load, or when [`configure`] fails.
pub fn init(cx: &mut App) -> anyhow::Result<Arc<AppState>> {
    let app_db = db::AppDatabase::new();
    let kvp = KeyValueStore::from_app_db(&app_db);
    cx.set_global(app_db);
    settings::init(cx);
    theme_settings::init(theme::LoadThemes::JustBase, cx);
    assets::Assets.load_fonts(cx)?;
    let fs = fs::RealFs::new(None, cx.background_executor().clone());
    <dyn fs::Fs>::set_global(fs.clone(), cx);
    let http = HttpClientWithUrl::new(Arc::new(BlockedHttpClient), "", None);
    let client = Client::new(Arc::new(clock::RealSystemClock), Arc::new(http), cx);
    let session = Session::new(std::process::id().to_string(), kvp);
    let session = cx.foreground_executor().block_on(session);
    let app_state = Arc::new(AppState {
        languages: Arc::new(LanguageRegistry::new(cx.background_executor().clone())),
        user_store: cx.new(|cx| UserStore::new(client.clone(), cx)),
        workspace_store: cx.new(|cx| WorkspaceStore::new(client.clone(), cx)),
        client,
        fs,
        build_window_options: |_, cx| window_options(cx),
        node_runtime: NodeRuntime::unavailable(),
        session: cx.new(|cx| AppSession::new(session, cx)),
    });
    AppState::set_global(app_state.clone(), cx);
    configure(cx)?;
    Ok(app_state)
}

/// Applies borer's theme and the app's settings, keymap and command palette over Zed's.
///
/// The theme and the settings layers are [`crate::app_settings::apply`]'s. It also gives
/// Zed's pickers their input, untrusts every folder, hides Zed's add folder action from the
/// palette, and saves each window's layout on quit.
///
/// # Arguments
///
/// * `cx` - Application context, Zed's settings store, themes and file system already set.
///
/// # Errors
///
/// Returns an error when borer's theme, the app's settings or the keymaps do not load.
pub fn configure(cx: &mut App) -> anyhow::Result<()> {
    crate::app_settings::apply(cx)?;
    ui_input::ERASED_EDITOR_FACTORY.get_or_init(|| erased_editor);
    trusted_worktrees::init(DbTrustedPaths::default(), cx);
    crate::actions::bind_keys(cx)?;
    command_palette::init(cx);
    let hidden = [TypeId::of::<AddFolderToProject>()];
    CommandPaletteFilter::update_global(cx, |filter, _| filter.hide_action_types(&hidden));
    cx.on_app_quit(flush_on_quit).detach();
    Ok(())
}

/// Returns a Zed single-line editor behind `ui_input`'s erased editor.
///
/// Every Zed picker, the command palette's among them, is built on it; Zed sets the same
/// factory in `editor::init`, which the app does not run.
///
/// # Arguments
///
/// * `window` - Window the editor is for.
/// * `cx` - Application context.
fn erased_editor(window: &mut Window, cx: &mut App) -> Arc<dyn ui_input::ErasedEditor> {
    cx.new(|cx| Editor::single_line(window, cx))
        .update(cx, |editor, cx| editor.erased(cx))
}

/// Returns the flush of every app window's pending layout to Zed's database, as Zed's own
/// workspace init does on quit.
///
/// # Arguments
///
/// * `cx` - Application context listing the windows.
fn flush_on_quit(cx: &mut App) -> impl Future<Output = ()> + use<> {
    let windows: Vec<_> = cx
        .windows()
        .into_iter()
        .filter_map(|window| window.downcast::<MultiWorkspace>())
        .collect();
    let mut cx = cx.to_async();
    async move { workspace::flush_windows_serialization(&windows, &mut cx).await }
}

/// Opens the first file dropped on one of `workspace`'s tabs as its binary, and refuses a
/// folder with a status line; nothing of a drop reaches Zed's open path.
///
/// # Arguments
///
/// * `workspace` - Workspace the tab belongs to.
/// * `dropped` - What was dropped.
/// * `cx` - Application context.
///
/// # Returns
///
/// `true` for dropped paths, which the tab took, `false` for anything else (a dragged tab),
/// which Zed's pane handles.
pub fn open_dropped(workspace: &WeakEntity<Workspace>, dropped: &dyn Any, cx: &mut App) -> bool {
    let Some(paths) = dropped.downcast_ref::<ExternalPaths>() else {
        return false;
    };
    let binary = workspace
        .upgrade()
        .and_then(|workspace| workspace.read(cx).panel::<FunctionsPanel>(cx))
        .map(|panel| panel.read(cx).binary().clone());
    if let (Some(binary), Some(path)) = (binary, paths.paths().first()) {
        let path = path.clone();
        binary.update(cx, |binary, cx| {
            if matches!(checked_metadata(&path), Ok(Some(meta)) if meta.is_dir()) {
                binary.set_status(format!("{} {REFUSED_FOLDER}", path.display()), cx);
            } else {
                binary.open_path(path, cx);
            }
        });
    }
    true
}

/// Returns the app's workspace for `window`: an empty local project, the functions panel,
/// the status line and the app's actions, its docks as the last run left them, loading
/// `path` when one is given.
///
/// # Arguments
///
/// * `app_state` - The app state from [`init`].
/// * `path` - Binary to open, if any.
/// * `window` - Window the workspace is for.
/// * `cx` - Application context.
pub fn new_workspace(
    app_state: &Arc<AppState>,
    path: Option<PathBuf>,
    window: &mut Window,
    cx: &mut App,
) -> Entity<Workspace> {
    let project = Project::local(
        app_state.client.clone(),
        app_state.node_runtime.clone(),
        app_state.user_store.clone(),
        app_state.languages.clone(),
        app_state.fs.clone(),
        None,
        LocalProjectFlags {
            init_worktree_trust: true,
            watch_global_configs: false,
        },
        cx,
    );
    let binary = cx.new(|_| Binary::default());
    let saved = saved_layout(cx);
    let in_right = saved.as_ref().is_ok_and(|docks| {
        docks
            .as_ref()
            .is_some_and(|docks| docks.right.active_panel.as_deref() == Some(PANEL_KEY))
    });
    let position = if in_right {
        DockPosition::Right
    } else {
        DockPosition::Left
    };
    let workspace = cx.new(|cx| {
        let id = WorkspaceId::from_i64(APP_WORKSPACE_ID);
        let mut workspace = Workspace::new(Some(id), project, app_state.clone(), window, cx);
        let weak = cx.weak_entity();
        let panel = cx.new(|cx| FunctionsPanel::new(weak, binary.clone(), position, window, cx));
        workspace.add_panel(panel, window, cx);
        let status = cx.new(|cx| StatusLine::new(binary.clone(), cx));
        workspace
            .status_bar()
            .update(cx, |bar, cx| bar.add_left_item(status, window, cx));
        register_actions(&mut workspace);
        workspace
    });
    match saved {
        Ok(Some(docks)) => workspace.update(cx, |workspace, cx| {
            workspace.set_dock_structure(docks, window, cx);
        }),
        Ok(None) => {}
        Err(err) => binary.update(cx, |binary, cx| {
            binary.set_status(format!("dock layout not restored: {err:#}"), cx);
        }),
    }
    workspace.update(cx, |workspace, cx| workspace.finish_dock_restoration(cx));
    let center = workspace.read(cx).active_pane().clone();
    center.update(cx, |pane, _| pane.set_should_display_welcome_page(false));
    keep_filled(&center, &workspace.downgrade(), window, cx);
    window
        .subscribe(
            &workspace,
            cx,
            |workspace, event: &workspace::Event, window, cx| {
                if let workspace::Event::PaneAdded(pane) = event {
                    keep_filled(pane, &workspace.downgrade(), window, cx);
                }
            },
        )
        .detach();
    if let Some(path) = path {
        binary.update(cx, |binary, cx| binary.open_path(path, cx));
    }
    workspace
}

/// Registers the app's workspace-wide actions on `workspace`.
///
/// # Arguments
///
/// * `workspace` - The workspace.
fn register_actions(workspace: &mut Workspace) {
    workspace
        .register_action(|workspace, _: &Open, _, cx| prompt_open(workspace, cx))
        .register_action(|workspace, _: &AddFolderToProject, _, cx| prompt_open(workspace, cx))
        .register_action(|workspace, _: &FocusFilter, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        })
        .register_action(|workspace, _: &ToggleFunctions, window, cx| {
            workspace.toggle_panel_focus::<FunctionsPanel>(window, cx);
        });
}

/// Opens the system file dialog for the binary of `workspace`'s functions panel.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `cx` - Application context.
fn prompt_open(workspace: &Workspace, cx: &mut App) {
    if let Some(panel) = workspace.panel::<FunctionsPanel>(cx) {
        let binary = panel.read(cx).binary().clone();
        binary.update(cx, |binary, cx| binary.prompt_open(cx));
    }
}

/// Returns the dock layout Zed saved for the app's empty workspace on an earlier run.
///
/// The workspace applies it as Zed does for every empty local workspace: it names the dock
/// the functions panel was in; panel sizes come back through Zed's own per-workspace store
/// when the panel is added.
///
/// # Arguments
///
/// * `cx` - Application context reading Zed's database.
///
/// # Returns
///
/// The saved layout, or `None` on a first run.
///
/// # Errors
///
/// Returns an error when the database cannot be read or the saved layout does not parse.
fn saved_layout(cx: &App) -> anyhow::Result<Option<DockStructure>> {
    let Some(saved) = KeyValueStore::global(cx).read_kvp(DEFAULT_DOCK_STATE_KEY)? else {
        return Ok(None);
    };
    serde_json::from_str(&saved)
        .map(Some)
        .context("parsing the saved docks")
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use borer_engine::analysis::render::{FunctionOrder, function_rows};
    use borer_engine::view::Ref;
    use command_palette::CommandPalette;
    use command_palette_hooks::CommandPaletteFilter;
    use db::kvp::KeyValueStore;
    use gpui::{
        Entity, ExternalPaths, FileDropEvent, TestAppContext, VisualTestContext, point, px, size,
    };
    use project::DisableAiSettings;
    use settings::Settings as _;
    use workspace::Panel as _;
    use workspace::dock::{DockPosition, PanelSizeState};
    use workspace::pane::{GoBack, GoForward};
    use workspace::{AddFolderToProject, AppState, MultiWorkspace, Workspace};

    use super::{DEFAULT_DOCK_STATE_KEY, REFUSED_FOLDER, configure, data_dir, new_workspace};
    use crate::decompile_item::{DecompileItem, TabMode, open_function};
    use crate::functions_panel::FunctionsPanel;
    use crate::measure::{CliMode, MeasurePhase, split_data_dir};
    use crate::worker::LoadedBinary;

    /// Entry of the sample program's caller, which calls [`CALLEE`].
    const CALLER: u64 = 0x1000;

    /// Entry of the sample program's callee.
    const CALLEE: u64 = 0x1030;

    /// Points Zed's paths at one data directory of the tests, once per process, so no test
    /// resolves the person's own Zed settings.
    ///
    /// # Panics
    ///
    /// Panics if the directory cannot be created.
    fn use_test_data_dir() {
        static ONCE: std::sync::Once = std::sync::Once::new();
        ONCE.call_once(|| {
            super::set_data_dir(&std::env::temp_dir().join("borer-app-tests")).unwrap();
        });
    }

    /// Starts Zed's test app state over a fresh in-memory database, configured as the app
    /// configures Zed.
    ///
    /// # Panics
    ///
    /// Panics if the app's settings or the keymaps do not load.
    fn init(cx: &mut TestAppContext) -> Arc<AppState> {
        use_test_data_dir();
        cx.update(|cx| {
            cx.set_global(db::AppDatabase::test_new());
            let app_state = AppState::test(cx);
            configure(cx).unwrap();
            app_state
        })
    }

    /// Returns the status line of `workspace`'s binary and empties it.
    ///
    /// # Panics
    ///
    /// Panics if the workspace has no functions panel.
    fn take_status(workspace: &Entity<Workspace>, cx: &mut VisualTestContext) -> String {
        let binary = workspace.read_with(cx, |workspace, cx| {
            workspace
                .panel::<FunctionsPanel>(cx)
                .unwrap()
                .read(cx)
                .binary()
                .clone()
        });
        binary.update(cx, |binary, cx| {
            let status = binary.status().to_owned();
            binary.set_status(String::new(), cx);
            status
        })
    }

    /// Drops `dir` from the system on the middle of the window.
    fn drop_on_center(dir: &Path, cx: &mut VisualTestContext) {
        cx.update(|window, cx| window.draw(cx).clear(cx));
        let size = cx.update(|window, _| window.viewport_size());
        let position = point(size.width * 0.5, size.height * 0.5);
        cx.simulate_event(FileDropEvent::Entered {
            position,
            paths: ExternalPaths([dir.to_path_buf()].into_iter().collect()),
        });
        cx.simulate_event(FileDropEvent::Submit { position });
        cx.run_until_parked();
    }

    /// Opens a window over the app's workspace and returns that workspace.
    fn open<'a>(
        app_state: &Arc<AppState>,
        cx: &'a mut TestAppContext,
    ) -> (Entity<Workspace>, &'a mut VisualTestContext) {
        let (root, cx) = cx.add_window_view(|window, cx| {
            let workspace = new_workspace(app_state, None, window, cx);
            MultiWorkspace::new(workspace, window, cx)
        });
        let workspace = root.read_with(cx, |root, _| root.workspace().clone());
        (workspace, cx)
    }

    /// Returns the hand-built sample program, a caller and its callee, as a loaded binary.
    fn sample() -> Arc<LoadedBinary> {
        let (program, analysis, overlay) = crate::code_view::tests::sample_program();
        let initial_rows = Arc::new(function_rows(
            &analysis,
            &overlay,
            None,
            FunctionOrder::Address,
            0,
            usize::MAX,
        ));
        Arc::new(LoadedBinary {
            path: PathBuf::from("sample.bin"),
            program: Arc::new(program),
            analysis: Arc::new(analysis),
            overlay: Arc::new(overlay),
            initial_rows,
        })
    }

    /// Opens the sample's caller in `workspace`'s active pane as `mode` says, focused.
    fn open_caller(workspace: &Entity<Workspace>, mode: TabMode, cx: &mut VisualTestContext) {
        let loaded = sample();
        workspace.update_in(cx, |workspace, window, cx| {
            open_function(workspace, loaded, CALLER, mode, true, window, cx);
        });
    }

    /// Returns the function and top line of the active decompile tab, once the work settled
    /// and a frame laid the tab out.
    fn shown(workspace: &Entity<Workspace>, cx: &mut VisualTestContext) -> Option<(u64, usize)> {
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        workspace.read_with(cx, |workspace, cx| {
            let item = workspace.active_item_as::<DecompileItem>(cx)?;
            let item = item.read(cx);
            Some((item.entry()?, item.top_line()))
        })
    }

    /// Asserts every name of `declared` is among the focused element's available actions.
    ///
    /// # Panics
    ///
    /// Panics if one is missing.
    fn assert_available(declared: &[&str], cx: &mut VisualTestContext) {
        cx.run_until_parked();
        let available = cx.update(|window, cx| window.available_actions(cx));
        for name in declared {
            assert!(
                available.iter().any(|action| action.name() == *name),
                "{name} is not available"
            );
        }
    }

    /// Every action of the `borer` namespace is available to Zed's command palette, with the
    /// functions panel focused and with a decompile tab focused.
    ///
    /// # Panics
    ///
    /// Panics if an action is missing in either place.
    #[gpui::test]
    fn every_borer_action_is_in_the_palette(cx: &mut TestAppContext) {
        every_borer_action_is_in_the_palette_steps(cx);
    }

    /// Runs the steps of [`every_borer_action_is_in_the_palette`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`every_borer_action_is_in_the_palette`] says.
    fn every_borer_action_is_in_the_palette_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        let declared: Vec<&str> = cx.update(|_, cx| {
            cx.all_action_names()
                .iter()
                .copied()
                .filter(|name| name.starts_with("borer::"))
                .collect()
        });
        assert!(!declared.is_empty());
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        assert_available(&declared, cx);
        open_caller(&workspace, TabMode::Permanent, cx);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), Some(CALLER));
        assert_available(&declared, cx);
    }

    /// A measurement run uses only the data directory its caller names, and refuses to run
    /// without one, never falling back to the person's; `--data-dir` leads the arguments.
    ///
    /// # Panics
    ///
    /// Panics if a measurement mode falls back to a directory of its own choosing.
    #[test]
    fn a_measurement_run_uses_only_the_data_dir_it_is_given() {
        let person = data_dir(&CliMode::Interactive(None), None).unwrap();
        let given = PathBuf::from("run-dir");
        for mode in [
            CliMode::FirstFrame,
            CliMode::ReportOpen(PathBuf::from("a.exe")),
            CliMode::MeasureMemory(PathBuf::from("a.exe")),
            CliMode::Measure(MeasurePhase::ListScroll),
        ] {
            assert!(data_dir(&mode, None).is_err());
            assert_eq!(data_dir(&mode, Some(given.clone())).unwrap(), given);
        }
        assert_ne!(person, given);
        let args: Vec<OsString> = ["--data-dir", "run-dir", "--first-frame"]
            .into_iter()
            .map(OsString::from)
            .collect();
        let (dir, rest) = split_data_dir(&args).unwrap();
        assert_eq!(dir, Some(given));
        assert_eq!(rest, &args[2..]);
        assert!(split_data_dir(&args[..1]).is_err());
    }

    /// Zed's command palette opens over the app, and what it lists holds every `borer`
    /// action but not Zed's open, open files or reload, which are offered nowhere, nor its
    /// add folder action, which is hidden.
    ///
    /// # Panics
    ///
    /// Panics if the palette does not open, misses a `borer` action or lists a Zed opener.
    #[gpui::test]
    fn the_palette_opens_with_the_app_actions_and_no_zed_opener(cx: &mut TestAppContext) {
        the_palette_opens_with_the_app_actions_and_no_zed_opener_steps(cx);
    }

    /// Runs the steps of [`the_palette_opens_with_the_app_actions_and_no_zed_opener`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_palette_opens_with_the_app_actions_and_no_zed_opener`] says.
    fn the_palette_opens_with_the_app_actions_and_no_zed_opener_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        cx.run_until_parked();
        let offered: Vec<String> = cx.update(|window, cx| {
            let filter = CommandPaletteFilter::try_global(cx);
            window
                .available_actions(cx)
                .into_iter()
                .filter(|action| filter.is_none_or(|filter| !filter.is_hidden(action.as_ref())))
                .map(|action| action.name().to_owned())
                .collect()
        });
        for name in [
            "workspace::Open",
            "workspace::OpenFiles",
            "workspace::Reload",
            "workspace::AddFolderToProject",
        ] {
            assert!(
                !offered.iter().any(|offered| offered == name),
                "{name} is offered"
            );
        }
        for name in [
            "borer::Open",
            "borer::FocusFilter",
            "borer::ToggleFunctions",
        ] {
            assert!(
                offered.iter().any(|offered| offered == name),
                "{name} is missing"
            );
        }
        let toggle = cx
            .update(|_, cx| cx.build_action("command_palette::Toggle", None))
            .unwrap();
        cx.update(|window, cx| window.dispatch_action(toggle, cx));
        cx.run_until_parked();
        let opened = workspace.read_with(cx, |workspace, cx| {
            workspace.active_modal::<CommandPalette>(cx).is_some()
        });
        assert!(opened);
    }

    /// A folder whose settings start a context server, dropped on a pane holding only the
    /// start tab and on a pane holding a decompile tab, or picked through Zed's add folder
    /// action, reaches the binary's loader each time and never becomes a project folder, and
    /// AI is off.
    ///
    /// # Panics
    ///
    /// Panics if the project gains a folder or AI is on.
    #[gpui::test]
    async fn a_dropped_or_added_folder_never_joins_the_project(cx: &mut TestAppContext) {
        a_dropped_or_added_folder_never_joins_the_project_steps(cx).await;
    }

    /// Runs the steps of [`a_dropped_or_added_folder_never_joins_the_project`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_dropped_or_added_folder_never_joins_the_project`] says.
    async fn a_dropped_or_added_folder_never_joins_the_project_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let dir = std::env::temp_dir().join(format!("borer-app-drop-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let settings = r#"{"context_servers": {"x": {"command": "calc.exe"}}}"#;
        app_state
            .fs
            .as_fake()
            .insert_tree(
                &dir,
                serde_json::json!({ ".zed": { "settings.json": settings } }),
            )
            .await;
        let (workspace, cx) = open(&app_state, cx);
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.close_panel::<FunctionsPanel>(window, cx);
        });
        drop_on_center(&dir, cx);
        assert!(take_status(&workspace, cx).ends_with(REFUSED_FOLDER));
        open_caller(&workspace, TabMode::Permanent, cx);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), Some(CALLER));
        drop_on_center(&dir, cx);
        assert!(take_status(&workspace, cx).ends_with(REFUSED_FOLDER));
        cx.dispatch_action(AddFolderToProject);
        cx.run_until_parked();
        cx.simulate_path_prompt_response(|_| Some(vec![dir.clone()]));
        cx.run_until_parked();
        assert!(take_status(&workspace, cx).starts_with("load failed"));
        std::fs::remove_dir_all(&dir).unwrap();
        let folders = workspace.read_with(cx, |workspace, cx| {
            workspace.project().read(cx).worktrees(cx).count()
        });
        assert_eq!(folders, 0);
        assert!(cx.update(|_, cx| DisableAiSettings::get_global(cx).disable_ai));
    }

    /// Zed's back and forward walk the places a decompile tab was left at: a jump inside
    /// the caller, then the caller's link to its callee.
    ///
    /// # Panics
    ///
    /// Panics if a step shows the wrong function or top line.
    #[gpui::test]
    fn back_returns_to_where_each_function_was_left(cx: &mut TestAppContext) {
        back_returns_to_where_each_function_was_left_steps(cx);
    }

    /// Runs the steps of [`back_returns_to_where_each_function_was_left`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`back_returns_to_where_each_function_was_left`] says.
    fn back_returns_to_where_each_function_was_left_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        cx.simulate_resize(size(px(800.0), px(160.0)));
        open_caller(&workspace, TabMode::Preview, cx);
        assert_eq!(shown(&workspace, cx), Some((CALLER, 0)));
        let caller = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<DecompileItem>(cx)
            })
            .unwrap();
        let (view, line) = caller.read_with(cx, |item, _| {
            let code = item.code().unwrap();
            (0..code.len())
                .find_map(|ix| {
                    let (view, line) = code.get(ix)?;
                    view.tokens(line)
                        .any(|(_, _, link)| link == Some(&Ref::Function(CALLEE)))
                        .then(|| (view.clone(), line))
                })
                .unwrap()
        });
        caller.update_in(cx, |item, _, cx| item.jump_to_line(1, cx));
        assert_eq!(shown(&workspace, cx), Some((CALLER, 1)));
        caller.update_in(cx, |item, window, cx| {
            item.follow(&view, &Ref::Function(CALLEE), (line, line), window, cx);
        });
        assert_eq!(shown(&workspace, cx), Some((CALLEE, 0)));
        for want in [(CALLER, 1), (CALLER, 0)] {
            cx.dispatch_action(GoBack);
            assert_eq!(shown(&workspace, cx), Some(want));
        }
        for want in [(CALLER, 1), (CALLEE, 0)] {
            cx.dispatch_action(GoForward);
            assert_eq!(shown(&workspace, cx), Some(want));
        }
    }

    /// A jump puts its line at the top of the tab although the line is already on screen,
    /// and going forward again restores a top line that was on screen.
    ///
    /// # Panics
    ///
    /// Panics if a jump or a restore leaves a different line at the top.
    #[gpui::test]
    fn a_jump_puts_its_line_at_the_top(cx: &mut TestAppContext) {
        a_jump_puts_its_line_at_the_top_steps(cx);
    }

    /// Runs the steps of [`a_jump_puts_its_line_at_the_top`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_jump_puts_its_line_at_the_top`] says.
    fn a_jump_puts_its_line_at_the_top_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open(&app_state, cx);
        cx.simulate_resize(size(px(800.0), px(160.0)));
        open_caller(&workspace, TabMode::Permanent, cx);
        assert_eq!(shown(&workspace, cx), Some((CALLER, 0)));
        let caller = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<DecompileItem>(cx)
            })
            .unwrap();
        caller.update_in(cx, |item, _, cx| item.jump_to_line(2, cx));
        assert_eq!(shown(&workspace, cx), Some((CALLER, 2)));
        cx.dispatch_action(GoBack);
        assert_eq!(shown(&workspace, cx), Some((CALLER, 0)));
        cx.dispatch_action(GoForward);
        assert_eq!(shown(&workspace, cx), Some((CALLER, 2)));
    }

    /// A saved layout that does not parse leaves the default layout, the panel open on the
    /// left, and says so in the status line.
    ///
    /// # Panics
    ///
    /// Panics if the panel is not open on the left or the status line is silent.
    #[gpui::test]
    async fn an_unreadable_layout_falls_back_to_the_default(cx: &mut TestAppContext) {
        an_unreadable_layout_falls_back_to_the_default_steps(cx).await;
    }

    /// Runs the steps of [`an_unreadable_layout_falls_back_to_the_default`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`an_unreadable_layout_falls_back_to_the_default`] says.
    async fn an_unreadable_layout_falls_back_to_the_default_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let kvp = cx.update(|cx| KeyValueStore::global(cx));
        kvp.write_kvp(DEFAULT_DOCK_STATE_KEY.to_owned(), "not json".to_owned())
            .await
            .unwrap();
        let (workspace, cx) = open(&app_state, cx);
        assert!(workspace.read_with(cx, |workspace, cx| {
            let dock = workspace.left_dock().read(cx);
            dock.is_open() && dock.panel::<FunctionsPanel>().is_some()
        }));
        assert!(take_status(&workspace, cx).starts_with("dock layout not restored"));
    }

    /// The functions panel moved to the right dock comes back open there in a new workspace
    /// over the same database.
    ///
    /// # Panics
    ///
    /// Panics if the panel is not in the right dock, open, after the move or the restore.
    #[gpui::test]
    async fn a_moved_panel_comes_back_in_its_dock(cx: &mut TestAppContext) {
        a_moved_panel_comes_back_in_its_dock_steps(cx).await;
    }

    /// Runs the steps of [`a_moved_panel_comes_back_in_its_dock`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_moved_panel_comes_back_in_its_dock`] says.
    async fn a_moved_panel_comes_back_in_its_dock_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let in_open_right_dock = |workspace: &Workspace, cx: &gpui::App| {
            let dock = workspace.right_dock().read(cx);
            dock.is_open() && dock.panel::<FunctionsPanel>().is_some()
        };
        {
            let (workspace, cx) = open(&app_state, cx);
            let panel = workspace
                .read_with(cx, |workspace, cx| workspace.panel::<FunctionsPanel>(cx))
                .unwrap();
            panel.update_in(cx, |panel, window, cx| {
                panel.set_position(DockPosition::Right, window, cx);
            });
            cx.run_until_parked();
            assert!(workspace.read_with(cx, |workspace, cx| in_open_right_dock(workspace, cx)));
            let flush = workspace.update_in(cx, |workspace, window, cx| {
                workspace.flush_serialization(window, cx)
            });
            flush.await;
            cx.run_until_parked();
        }
        let (workspace, cx) = open(&app_state, cx);
        assert!(workspace.read_with(cx, |workspace, cx| in_open_right_dock(workspace, cx)));
    }

    /// The functions panel's width and its dock's visibility, saved through Zed's
    /// persistence, come back in a new workspace over the same database.
    ///
    /// # Panics
    ///
    /// Panics if the width or the visibility is not restored.
    #[gpui::test]
    async fn dock_layout_survives_a_new_workspace(cx: &mut TestAppContext) {
        dock_layout_survives_a_new_workspace_steps(cx).await;
    }

    /// Runs the steps of [`dock_layout_survives_a_new_workspace`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`dock_layout_survives_a_new_workspace`] says.
    async fn dock_layout_survives_a_new_workspace_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let width = px(333.0);
        {
            let (workspace, cx) = open(&app_state, cx);
            let open_at_start =
                workspace.read_with(cx, |workspace, cx| workspace.left_dock().read(cx).is_open());
            assert!(open_at_start);
            let flush = workspace.update_in(cx, |workspace, window, cx| {
                let state = PanelSizeState {
                    size: Some(width),
                    flex: None,
                };
                workspace.set_panel_size_state::<FunctionsPanel>(state, window, cx);
                workspace.close_panel::<FunctionsPanel>(window, cx);
                workspace.flush_serialization(window, cx)
            });
            flush.await;
            cx.run_until_parked();
        }
        let (workspace, cx) = open(&app_state, cx);
        workspace.read_with(cx, |workspace, cx| {
            let saved = workspace.panel_size_state::<FunctionsPanel>(cx);
            assert_eq!(saved.and_then(|state| state.size), Some(width));
            assert!(!workspace.left_dock().read(cx).is_open());
        });
    }
}
