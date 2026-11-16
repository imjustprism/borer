//! The app's window: Zed's [`Workspace`] over an empty local [`Project`], with the functions
//! panel in its left dock and the load status in its status bar.
//!
//! Zed's settings, themes, keymap, command palette and persistence run under the app's own
//! data directory. Nothing signs in, updates, reports telemetry or collaborates:
//! `client::init`, `Project::init` and Zed's auto-update, crash, telemetry and call crates are
//! never started, the client's HTTP is Zed's `BlockedHttpClient`, and Node is unavailable.

use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Context as _;
use client::{Client, UserStore};
use db::kvp::KeyValueStore;
use gpui::{
    App, AppContext as _, Bounds, Context, Entity, Window, WindowBounds, WindowOptions, px, size,
};
use http_client::{BlockedHttpClient, HttpClientWithUrl};
use language::LanguageRegistry;
use node_runtime::NodeRuntime;
use project::{LocalProjectFlags, Project};
use session::{AppSession, Session};
use workspace::{AppState, DockStructure, Workspace, WorkspaceId, WorkspaceStore};

use crate::actions::{FocusFilter, Open, ToggleFunctions};
use crate::binary::{Binary, StatusLine};
use crate::functions_panel::FunctionsPanel;

/// Directory of the app's settings, keymap, database and logs under the platform's local
/// data directory, kept apart from an installed Zed's.
const DATA_DIR_NAME: &str = "borer-app";

/// Id of the app's one workspace in its own database, the same on every run, so Zed keys
/// the saved panel sizes the same way each time.
const APP_WORKSPACE_ID: i64 = 1;

/// Zed's key-value key for the dock layout of an empty local workspace (private to
/// `workspace::persistence`, which writes it on every serialization).
const DEFAULT_DOCK_STATE_KEY: &str = "default_dock_state";

/// Default window width in logical pixels.
const WINDOW_WIDTH_PX: f32 = 1280.0;

/// Default window height in logical pixels.
const WINDOW_HEIGHT_PX: f32 = 800.0;

/// Points Zed's settings, keymap, database and logs at the app's own data directory.
///
/// Must run before anything reads Zed's data or config directory.
///
/// # Errors
///
/// Returns an error when the platform has no local data directory, the directory cannot be
/// created, or its path is not UTF-8.
pub fn set_data_dir() -> anyhow::Result<()> {
    let dir = dirs::data_local_dir()
        .context("the platform has no local data directory")?
        .join(DATA_DIR_NAME);
    std::fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;
    let name = dir
        .to_str()
        .with_context(|| format!("the data directory {} is not UTF-8", dir.display()))?;
    paths::set_custom_data_dir(name);
    Ok(())
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
/// Returns an error when Zed's fonts or the keymaps do not load.
pub fn init(cx: &mut App) -> anyhow::Result<Arc<AppState>> {
    let app_db = db::AppDatabase::new();
    let kvp = KeyValueStore::from_app_db(&app_db);
    cx.set_global(app_db);
    settings::init(cx);
    theme_settings::init(theme::LoadThemes::All(Box::new(assets::Assets)), cx);
    assets::Assets.load_fonts(cx)?;
    crate::actions::bind_keys(cx)?;
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
    editor::init(cx);
    workspace::init(app_state.clone(), cx);
    command_palette::init(cx);
    Ok(app_state)
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
            init_worktree_trust: false,
            watch_global_configs: false,
        },
        cx,
    );
    let binary = cx.new(|_| Binary::default());
    let workspace = cx.new(|cx| {
        let id = WorkspaceId::from_i64(APP_WORKSPACE_ID);
        let mut workspace = Workspace::new(Some(id), project, app_state.clone(), window, cx);
        let weak = cx.weak_entity();
        let panel = cx.new(|cx| FunctionsPanel::new(weak, binary.clone(), window, cx));
        workspace.add_panel(panel, window, cx);
        let status = cx.new(|cx| StatusLine::new(binary.clone(), cx));
        workspace
            .status_bar()
            .update(cx, |bar, cx| bar.add_left_item(status, window, cx));
        register_actions(&mut workspace);
        workspace
    });
    if let Err(err) = workspace.update(cx, |workspace, cx| restore_layout(workspace, window, cx)) {
        binary.update(cx, |binary, cx| {
            binary.set_status(format!("dock layout not restored: {err:#}"), cx);
        });
    }
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
        .register_action(|workspace, _: &Open, _, cx| {
            if let Some(panel) = workspace.panel::<FunctionsPanel>(cx) {
                let binary = panel.read(cx).binary().clone();
                binary.update(cx, |binary, cx| binary.prompt_open(cx));
            }
        })
        .register_action(|workspace, _: &FocusFilter, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        })
        .register_action(|workspace, _: &ToggleFunctions, window, cx| {
            workspace.toggle_panel_focus::<FunctionsPanel>(window, cx);
        });
}

/// Applies the dock layout Zed saved for the app's empty workspace on an earlier run.
///
/// It does so as Zed does for every empty local workspace; panel sizes come back through
/// Zed's own per-workspace store when the panel is added.
///
/// # Arguments
///
/// * `workspace` - The workspace, its panels added.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
///
/// # Errors
///
/// Returns an error when the database cannot be read or the saved layout does not parse.
fn restore_layout(
    workspace: &Workspace,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) -> anyhow::Result<()> {
    let Some(saved) = KeyValueStore::global(cx).read_kvp(DEFAULT_DOCK_STATE_KEY)? else {
        return Ok(());
    };
    let docks: DockStructure = serde_json::from_str(&saved).context("parsing the saved docks")?;
    workspace.set_dock_structure(docks, window, cx);
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::sync::Arc;

    use borer_engine::analysis::render::{FunctionOrder, function_rows};
    use borer_engine::view::Ref;
    use gpui::{Entity, TestAppContext, VisualTestContext, px, size};
    use workspace::dock::PanelSizeState;
    use workspace::pane::{GoBack, GoForward};
    use workspace::{AppState, MultiWorkspace, Workspace};

    use super::new_workspace;
    use crate::decompile_item::{DecompileItem, TabMode, open_function};
    use crate::functions_panel::FunctionsPanel;
    use crate::worker::LoadedBinary;

    /// Entry of the sample program's caller, which calls [`CALLEE`].
    const CALLER: u64 = 0x1000;

    /// Entry of the sample program's callee.
    const CALLEE: u64 = 0x1030;

    /// Starts Zed's test app state over a fresh in-memory database, with the app's keymap,
    /// Zed's editor, workspace and command palette.
    ///
    /// # Panics
    ///
    /// Panics if the keymaps do not load.
    fn init(cx: &mut TestAppContext) -> Arc<AppState> {
        cx.update(|cx| {
            cx.set_global(db::AppDatabase::test_new());
            let app_state = AppState::test(cx);
            crate::actions::bind_keys(cx).unwrap();
            editor::init(cx);
            workspace::init(app_state.clone(), cx);
            command_palette::init(cx);
            app_state
        })
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

    /// Returns the function and top line of the active decompile tab, once the work settled.
    fn shown(workspace: &Entity<Workspace>, cx: &mut VisualTestContext) -> Option<(u64, usize)> {
        cx.run_until_parked();
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
        let loaded = sample();
        workspace.update_in(cx, |workspace, window, cx| {
            open_function(
                workspace,
                loaded,
                CALLER,
                TabMode::Permanent,
                true,
                window,
                cx,
            );
        });
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), Some(CALLER));
        assert_available(&declared, cx);
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
        let loaded = sample();
        workspace.update_in(cx, |workspace, window, cx| {
            open_function(
                workspace,
                loaded,
                CALLER,
                TabMode::Preview,
                true,
                window,
                cx,
            );
        });
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
