//! The app's window: Zed's [`Workspace`] over an empty local [`Project`], with nothing docked
//! until a binary loads, then the functions panel in its left dock, and the load status in
//! its status bar.
//!
//! Zed's settings, themes, keymap, command palette and persistence run under the app's own
//! data directory. Nothing signs in, updates, reports telemetry or collaborates:
//! `client::init`, `Project::init` and Zed's auto-update, crash, telemetry and call crates are
//! never started, the client's HTTP is Zed's `BlockedHttpClient`, and Node is unavailable.
//!
//! No path ever becomes a project folder, so no folder's settings, context servers, git or
//! login shell run: `workspace::init` and `editor::init`, which register Zed's open, open
//! files, reload and new file actions, are not started; the command table unbinds their keys;
//! a dropped file reaches a tab, and every pane keeps one ([`keep_filled`]); Zed's add folder
//! action opens a binary instead; AI is off and every folder untrusted.

use std::any::{Any, TypeId};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Context as _;
use borer_engine::program::checked_metadata;
use client::{Client, UserStore};
use command_palette_hooks::CommandPaletteFilter;
use db::kvp::KeyValueStore;
use editor::Editor;
use gpui::{
    AnyWindowHandle, App, AppContext as _, Bounds, Context, Entity, ExternalPaths, PromptLevel,
    SharedString, TaskExt as _, TitlebarOptions, Window, WindowBounds, WindowHandle, WindowOptions,
    point, px, size,
};
use http_client::{BlockedHttpClient, HttpClientWithUrl};
use language::LanguageRegistry;
use node_runtime::NodeRuntime;
use project::trusted_worktrees::{self, DbTrustedPaths};
use project::{LocalProjectFlags, Project};
use search::BufferSearchBar;
use session::{AppSession, Session};
use workspace::dock::{DockPosition, PanelButtons};
use workspace::{
    AddFolderToProject, AppState, DockData, DockStructure, Pane, Workspace, WorkspaceId,
    WorkspaceStore,
};

use crate::actions::{CloseBinary, MinimizeWindow, Open, ZoomWindow};
use crate::app_dirs::with_host_env;
use crate::binary::{Binary, StatusLine};
use crate::commands;
use crate::decompile_item::DecompileItem;
use crate::functions_panel::FunctionsPanel;
use crate::linear_item::LinearItem;
use crate::measure::CliMode;
use crate::panels::{PANELS, add_panels};
use crate::shell::Shell;
use crate::start_item::keep_filled;
use crate::theme_import::read_dropped;
use crate::user_themes::is_theme_path;

/// The app's window id, which desktops match to its launcher entry.
const APP_ID: &str = "borer-app";

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

/// Narrowest window in logical pixels.
const WINDOW_MIN_WIDTH_PX: f32 = 640.0;

/// Shortest window in logical pixels.
const WINDOW_MIN_HEIGHT_PX: f32 = 400.0;

/// Offset in logical pixels of macOS's traffic lights from the window's top left corner.
const TRAFFIC_LIGHT_PX: f32 = 9.0;

/// Returns the data directory of a run in `mode`.
///
/// That is `given` when the command line names one, else the app's own for a person
/// ([`crate::app_dirs::Env::borer`]). A measurement must be given one, a fresh directory
/// its caller creates and removes, so it neither reads nor writes the person's layout and
/// nothing it leaves outlives the caller.
///
/// # Arguments
///
/// * `mode` - The run's mode.
/// * `given` - The directory `--data-dir` names, if any.
///
/// # Errors
///
/// Returns an error when a measurement names no directory or the platform's directories
/// do not resolve.
pub fn data_dir(mode: &CliMode, given: Option<PathBuf>) -> anyhow::Result<PathBuf> {
    if let Some(dir) = given {
        return Ok(dir);
    }
    match mode {
        CliMode::Interactive(_) => Ok(with_host_env(|env| env.borer())?.data),
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

/// Points Zed's database and logs at `dir`, and creates the app's config directory
/// ([`crate::app_dirs::config_dir`]), which the person's settings and themes live in.
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
    let config = crate::app_dirs::config_dir();
    std::fs::create_dir_all(config).with_context(|| format!("creating {}", config.display()))
}

/// Returns the options of a new app window.
///
/// The window is centered at the default size, titled `borer`, with the system's title bar
/// hidden so the app draws its own ([`crate::title_bar`]), and hidden until its first frame
/// is drawn, so it never shows empty.
///
/// Linux keeps the system's decorations: Zed's client-side ones wrap only the workspace,
/// not the title bar the app draws over it.
///
/// # Arguments
///
/// * `cx` - Application context reading the displays.
#[must_use]
pub fn window_options(cx: &App) -> WindowOptions {
    let bounds = Bounds::centered(None, size(px(WINDOW_WIDTH_PX), px(WINDOW_HEIGHT_PX)), cx);
    WindowOptions {
        window_bounds: Some(WindowBounds::Windowed(bounds)),
        titlebar: Some(TitlebarOptions {
            title: Some(SharedString::new_static("borer")),
            appears_transparent: true,
            traffic_light_position: Some(point(px(TRAFFIC_LIGHT_PX), px(TRAFFIC_LIGHT_PX))),
        }),
        focus: true,
        show: false,
        window_min_size: Some(size(px(WINDOW_MIN_WIDTH_PX), px(WINDOW_MIN_HEIGHT_PX))),
        app_id: Some(APP_ID.to_owned()),
        icon: window_icon(),
        ..WindowOptions::default()
    }
}

/// Returns the app icon at 128 px, the window icon GPUI sets on X11.
///
/// Other platforms take their window icon elsewhere: Windows from the icon resource
/// `build.rs` embeds, macOS from the app bundle, Wayland from the desktop entry named by
/// the window's app id.
///
/// # Returns
///
/// `None` if the embedded PNG does not decode, which `window_icon_decodes` rules out.
fn window_icon() -> Option<Arc<image::RgbaImage>> {
    let png = include_bytes!("../../../packaging/borer-app/icons/128.png");
    let icon = image::load_from_memory_with_format(png, image::ImageFormat::Png).ok()?;
    Some(Arc::new(icon.into_rgba8()))
}

/// Opens an app window over a new workspace, loading `path` when one is given, and shows
/// it.
///
/// # Arguments
///
/// * `app_state` - The app state from [`init`].
/// * `path` - Binary to open, if any.
/// * `cx` - Application context.
///
/// # Returns
///
/// The window.
///
/// # Errors
///
/// Returns an error when the platform does not open the window.
pub fn open_window(
    app_state: &Arc<AppState>,
    path: Option<PathBuf>,
    cx: &mut App,
) -> anyhow::Result<WindowHandle<Shell>> {
    let window = cx.open_window(window_options(cx), |window, cx| {
        let app = new_workspace(app_state, path, window, cx);
        cx.new(|cx| Shell::new(app, window, cx))
    })?;
    activate(window.into(), cx)?;
    Ok(window)
}

/// Brings `window` forward and shows it: a window opened hidden ([`window_options`])
/// appears only once activated, as Zed's own windows do.
///
/// # Arguments
///
/// * `window` - The window.
/// * `cx` - Application context.
///
/// # Errors
///
/// Returns an error when the window is gone.
pub fn activate(window: AnyWindowHandle, cx: &mut App) -> anyhow::Result<()> {
    window.update(cx, |_, window, _| window.activate_window())
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
/// Zed's pickers their input, untrusts every folder, and saves each window's layout on quit.
/// It hides from the palette Zed's add folder action and the two Zed actions that would
/// write Zed's own settings file, not the app's ([`crate::app_dirs`]): edit predictions for
/// all files and the editor's tab bar, which no default key binds.
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
    commands::bind_keys(cx)?;
    cx.set_menus(commands::menus(cx));
    command_palette::init(cx);
    search::buffer_search::init(cx);
    let hidden = [
        TypeId::of::<AddFolderToProject>(),
        TypeId::of::<workspace::ToggleEditPrediction>(),
        TypeId::of::<editor::actions::ToggleTabBar>(),
    ];
    CommandPaletteFilter::update_global(cx, |filter, _| filter.hide_action_types(&hidden));
    cx.on_app_quit(crate::shell::flush_windows).detach();
    cx.on_action(|_: &zed_actions::Quit, cx| cx.quit());
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

/// Opens the first file dropped on a tab as the window's binary, and refuses a folder with
/// a status line; nothing of a drop reaches Zed's open path.
///
/// A dropped `.json` file is read in the background as a theme file: one that parses as a
/// theme family, or as JSON with a top-level `themes` key, opens its import report with
/// what it holds or why it does not parse ([`crate::theme_import::read_dropped`]); any
/// other opens as a binary like any other file.
///
/// # Arguments
///
/// * `binary` - The window's binary.
/// * `dropped` - What was dropped.
/// * `window` - Window the tab is in.
/// * `cx` - Application context.
///
/// # Returns
///
/// `true` for dropped paths, which the tab took, `false` for anything else (a dragged tab),
/// which Zed's pane handles.
pub fn open_dropped(
    binary: &Entity<Binary>,
    dropped: &dyn Any,
    window: &mut Window,
    cx: &mut App,
) -> bool {
    let Some(paths) = dropped.downcast_ref::<ExternalPaths>() else {
        return false;
    };
    if let Some(path) = paths.paths().first() {
        let path = path.clone();
        let folder = matches!(checked_metadata(&path), Ok(Some(meta)) if meta.is_dir());
        let shell = window.root::<Shell>().flatten();
        let workspace = shell.map(|shell| shell.read(cx).workspace().downgrade());
        if let Some(workspace) = workspace.filter(|_| !folder && is_theme_path(&path)) {
            let (read, binary) = (
                read_dropped(<dyn fs::Fs>::global(cx), path.clone(), cx),
                binary.clone(),
            );
            window
                .spawn(cx, async move |cx| match read.await {
                    Some(read) => crate::theme_import::show(&workspace, read, cx),
                    None => {
                        binary.update(cx, |binary, cx| binary.open_path(path, cx));
                        Ok(())
                    }
                })
                .detach_and_log_err(cx);
            return true;
        }
        binary.update(cx, |binary, cx| {
            if folder {
                binary.set_status(format!("{} {REFUSED_FOLDER}", path.display()), cx);
            } else {
                binary.open_path(path, cx);
            }
        });
    }
    true
}

/// Expands, inside an `impl Item`, to the methods every tab over one snapshot shares: the
/// file's path as its tooltip, and a dropped path opened through [`open_dropped`].
///
/// The item holds the snapshot in `loaded` and the window's binary in `binary`.
macro_rules! snapshot_tab {
    () => {
        fn tab_tooltip_text(&self, _cx: &gpui::App) -> Option<gpui::SharedString> {
            Some(self.loaded.path.display().to_string().into())
        }

        fn handle_drop(
            &self,
            _active_pane: &workspace::Pane,
            dropped: &dyn std::any::Any,
            window: &mut gpui::Window,
            cx: &mut gpui::App,
        ) -> bool {
            crate::app_view::open_dropped(&self.binary, dropped, window, cx)
        }
    };
}
pub(crate) use snapshot_tab;

/// A window's workspace and the binary it has open.
#[derive(Debug, Clone)]
pub struct AppWindow {
    /// Zed's workspace: panes, docks and status bar.
    pub workspace: Entity<Workspace>,
    /// The window's binary.
    pub binary: Entity<Binary>,
}

/// Returns the app's workspace for `window` and its binary: an empty local project, the
/// status line and the app's actions, loading `path` when one is given.
///
/// Nothing is docked until a binary loads: the functions panel is added with the first
/// loaded binary, in the dock and state the last run left it ([`dock_panels`]).
///
/// # Arguments
///
/// * `app_state` - The app state from [`init`].
/// * `path` - Binary to open, if any.
/// * `window` - Window the workspace is for.
/// * `cx` - Application context.
///
/// # Returns
///
/// The workspace and the window's binary.
pub fn new_workspace(
    app_state: &Arc<AppState>,
    path: Option<PathBuf>,
    window: &mut Window,
    cx: &mut App,
) -> AppWindow {
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
    let binary = cx.new(|cx| Binary::new(cx));
    let workspace = cx.new(|cx| {
        let id = WorkspaceId::from_i64(APP_WORKSPACE_ID);
        let mut workspace = Workspace::new(Some(id), project, app_state.clone(), window, cx);
        crate::overview::open_on_load(&binary, window, cx);
        let status = cx.new(|cx| StatusLine::new(binary.clone(), cx));
        workspace
            .status_bar()
            .update(cx, |bar, cx| bar.add_left_item(status, window, cx));
        crate::status::add_items(&mut workspace, &binary, window, cx);
        workspace.status_bar().update(cx, |bar, cx| {
            while let Some(ix) = bar.position_of_item::<PanelButtons>() {
                bar.remove_item_at(ix, cx);
            }
        });
        crate::features::register(&mut workspace, &binary);
        workspace
    });
    let saved = saved_layout(cx).unwrap_or_else(|err| {
        binary.update(cx, |binary, cx| {
            binary.set_status(format!("dock layout not restored: {err:#}"), cx);
        });
        None
    });
    workspace.update(cx, |workspace, cx| workspace.finish_dock_restoration(cx));
    let app = AppWindow { workspace, binary };
    let center = app.workspace.read(cx).active_pane().clone();
    center.update(cx, |pane, _| pane.set_should_display_welcome_page(false));
    keep_filled(&center, &app.binary, window, cx);
    add_search_bar(&center, window, cx);
    center.update(cx, |pane, cx| pane.focus_active_item(window, cx));
    let pane_binary = app.binary.clone();
    window
        .subscribe(
            &app.workspace,
            cx,
            move |_, event: &workspace::Event, window, cx| {
                if let workspace::Event::PaneAdded(pane) = event {
                    keep_filled(pane, &pane_binary, window, cx);
                    add_search_bar(pane, window, cx);
                }
            },
        )
        .detach();
    let weak = app.workspace.downgrade();
    window
        .observe(&app.binary, cx, move |binary, window, cx| {
            if let Some(workspace) = weak.upgrade() {
                dock_panels(&workspace, &binary, saved.as_ref(), window, cx);
            }
        })
        .detach();
    if let Some(path) = path {
        app.binary
            .update(cx, |binary, cx| binary.open_path(path, cx));
    }
    app
}

/// Gives `pane` Zed's buffer search bar, which finds text in the active code tab.
///
/// # Arguments
///
/// * `pane` - The pane.
/// * `window` - Window the pane is in.
/// * `cx` - Application context.
fn add_search_bar(pane: &Entity<Pane>, window: &mut Window, cx: &mut App) {
    let bar = cx.new(|cx| BufferSearchBar::new(None, window, cx));
    pane.update(cx, |pane, cx| {
        pane.toolbar()
            .update(cx, |toolbar, cx| toolbar.add_item(bar, window, cx));
    });
}

/// Adds every panel of [`PANELS`] to `workspace` once `binary` has loaded, when none is
/// docked yet.
///
/// Each panel goes in the dock `saved` shows it in ([`add_panels`]), the docks opened or
/// closed as `saved` left them when it names any panel; then the functions panel lists the
/// binary's functions and opens the first.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
/// * `saved` - The dock layout an earlier run left, if any.
/// * `window` - Window the workspace is in.
/// * `cx` - Application context.
pub fn dock_panels(
    workspace: &Entity<Workspace>,
    binary: &Entity<Binary>,
    saved: Option<&DockStructure>,
    window: &mut Window,
    cx: &mut App,
) {
    let docked = workspace.read(cx).panel::<FunctionsPanel>(cx).is_some();
    if docked || binary.read(cx).loaded().is_none() {
        return;
    }
    let named = |data: &DockData| {
        let active = data.active_panel.as_deref();
        PANELS.iter().any(|spec| active == Some(spec.key))
    };
    let saved = saved.filter(|docks| {
        [&docks.left, &docks.right, &docks.bottom]
            .into_iter()
            .any(named)
    });
    workspace.update(cx, |workspace, cx| {
        add_panels(workspace, binary, saved, window, cx);
        if let Some(docks) = saved {
            workspace.set_dock_structure(docks.clone(), window, cx);
        }
    });
    if let Some(panel) = workspace.read(cx).panel::<FunctionsPanel>(cx) {
        panel.update(cx, |panel, cx| panel.follow(window, cx));
    }
}

/// Adds a functions panel over `binary` to `workspace`'s dock at `position`, open, and
/// returns it; it lists nothing until told to or until the binary next changes.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
/// * `position` - The dock the panel goes in.
/// * `window` - Window the workspace is in.
/// * `cx` - Application context.
pub fn add_functions_panel(
    workspace: &Entity<Workspace>,
    binary: &Entity<Binary>,
    position: DockPosition,
    window: &mut Window,
    cx: &mut App,
) -> Entity<FunctionsPanel> {
    workspace.update(cx, |workspace, cx| {
        let weak = cx.weak_entity();
        let panel = cx.new(|cx| FunctionsPanel::new(weak, binary.clone(), position, window, cx));
        workspace.add_panel(panel.clone(), window, cx);
        panel
    })
}

/// Registers the file and window actions on `workspace`, over the window's `binary`:
/// open, Zed's add folder (which opens a binary), close, the settings file, minimize, zoom
/// and about.
///
/// Zed's theme-mode toggle is answered here, before Zed's own handler, so it writes the
/// app's settings file as [`crate::actions::ToggleTheme`] does.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let (open, add, close, settings) = (
        binary.clone(),
        binary.clone(),
        binary.clone(),
        binary.clone(),
    );
    commands::register(workspace, binary, move |_, _: &Open, _, cx| {
        open.update(cx, |binary, cx| binary.prompt_open(cx));
    });
    commands::register(
        workspace,
        binary,
        move |_, _: &AddFolderToProject, _, cx| {
            add.update(cx, |binary, cx| binary.prompt_open(cx));
        },
    );
    commands::register(
        workspace,
        binary,
        move |workspace, _: &CloseBinary, window, cx| {
            close_binary(workspace, &close, window, cx);
        },
    );
    commands::register(
        workspace,
        binary,
        move |_, _: &zed_actions::OpenSettingsFile, _, cx| {
            open_settings_file(&settings, cx);
        },
    );
    commands::register(workspace, binary, |_, _: &MinimizeWindow, window, _| {
        window.minimize_window();
    });
    commands::register(workspace, binary, |_, _: &ZoomWindow, window, _| {
        window.zoom_window();
    });
    commands::register(
        workspace,
        binary,
        |_, _: &zed_actions::About, window, cx| {
            about(window, cx);
        },
    );
}

/// Closes `binary`, takes every panel of [`PANELS`] out of its dock and closes its code and
/// linear listing tabs, which leaves each pane its start tab.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
fn close_binary(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    binary.update(cx, Binary::close);
    for spec in PANELS {
        (spec.remove)(workspace, window, cx);
    }
    for pane in workspace.panes().to_vec() {
        let pane_ref = pane.read(cx);
        let code = pane_ref
            .items_of_type::<DecompileItem>()
            .map(|tab| tab.entity_id());
        let linear = pane_ref
            .items_of_type::<LinearItem>()
            .map(|tab| tab.entity_id());
        let tabs: Vec<_> = code.chain(linear).collect();
        pane.update(cx, |pane, cx| {
            for tab in tabs {
                pane.remove_item(tab, false, false, window, cx);
            }
        });
    }
}

/// Opens the person's settings file with the system's editor for it, or says on the status
/// line that there is none yet.
///
/// # Arguments
///
/// * `binary` - The window's binary, whose status line says what happened.
/// * `cx` - Application context.
fn open_settings_file(binary: &Entity<Binary>, cx: &mut App) {
    let path = &crate::app_dirs::settings_file();
    match checked_metadata(path) {
        Ok(Some(_)) => cx.open_with_system(path),
        Ok(None) => binary.update(cx, |binary, cx| {
            let why = format!("no settings file yet at {}", path.display());
            binary.set_status(why, cx);
        }),
        Err(err) => binary.update(cx, |binary, cx| {
            binary.set_status(format!("settings file not opened: {err:#}"), cx);
        }),
    }
}

/// Shows the app's name, version and license in a dialog.
///
/// # Arguments
///
/// * `window` - Window the dialog opens over.
/// * `cx` - Application context.
fn about(window: &mut Window, cx: &mut App) {
    let detail = format!(
        "borer-app {}, license {}",
        env!("CARGO_PKG_VERSION"),
        env!("CARGO_PKG_LICENSE")
    );
    let answer = window.prompt(PromptLevel::Info, "borer", Some(&detail), &["OK"], cx);
    cx.background_spawn(answer).detach();
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
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use borer_engine::analysis::name_of;
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
    use workspace::dock::{DockPosition, PanelSizeState};
    use workspace::pane::{GoBack, GoForward};
    use workspace::{AddFolderToProject, AppState, Workspace};
    use workspace::{Item as _, Panel as _};

    use super::{
        AppWindow, DEFAULT_DOCK_STATE_KEY, REFUSED_FOLDER, configure, data_dir, new_workspace,
        window_icon,
    };
    use crate::actions::{Open, ToggleFunctionColumns};
    use crate::binary::{Binary, StatusLine};
    use crate::call_tree_panel::{CallTreePanel, OWN_ACTIONS};
    use crate::decompile_item::{DecompileItem, Form, TabMode};
    use crate::function_columns::Columns;
    use crate::functions_panel::FunctionsPanel;
    use crate::measure::{CliMode, MeasurePhase, split_data_dir};
    use crate::places::{self, Opening, Place};
    use crate::shell::Shell;
    use crate::start_item::StartItem;
    use crate::worker::LoadedBinary;

    /// Entry of the sample program's caller, which calls [`CALLEE`].
    pub(crate) const CALLER: u64 = 0x1000;

    /// Entry of the sample program's callee.
    pub(crate) const CALLEE: u64 = 0x1030;

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
    /// configures Zed, every load reading no packs or symbol cache of the machine's.
    ///
    /// # Panics
    ///
    /// Panics if the app's settings or the keymaps do not load.
    pub(crate) fn init(cx: &mut TestAppContext) -> Arc<AppState> {
        use_test_data_dir();
        cx.update(|cx| {
            cx.set_global(db::AppDatabase::test_new());
            cx.set_global(crate::stored::FixedSources::default());
            let app_state = AppState::test(cx);
            configure(cx).unwrap();
            app_state
        })
    }

    /// Returns the status line of the window's binary and empties it.
    pub(crate) fn take_status(app: &AppWindow, cx: &mut VisualTestContext) -> String {
        app.binary.update(cx, |binary, cx| {
            let status = binary.status().to_owned();
            binary.set_status(String::new(), cx);
            status
        })
    }

    /// Drops `dir` from the system on the middle of the window.
    pub(crate) fn drop_on_center(dir: &Path, cx: &mut VisualTestContext) {
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

    /// Opens a window over the app's workspace and returns that workspace and its binary.
    ///
    /// # Panics
    ///
    /// Panics if the window's root is not built.
    pub(crate) fn open<'a>(
        app_state: &Arc<AppState>,
        cx: &'a mut TestAppContext,
    ) -> (AppWindow, &'a mut VisualTestContext) {
        let mut opened = None;
        let (_, cx) = cx.add_window_view(|window, cx| {
            let app = new_workspace(app_state, None, window, cx);
            opened = Some(app.clone());
            Shell::new(app, window, cx)
        });
        (opened.unwrap(), cx)
    }

    /// Shows the sample program as the window's loaded binary, which docks the functions
    /// panel, and returns the panel.
    ///
    /// # Panics
    ///
    /// Panics if no panel is docked.
    pub(crate) fn load_sample(
        app: &AppWindow,
        cx: &mut VisualTestContext,
    ) -> Entity<FunctionsPanel> {
        app.binary
            .update(cx, |binary, cx| binary.show_loaded(sample(), cx));
        cx.run_until_parked();
        app.workspace
            .read_with(cx, |workspace, cx| workspace.panel::<FunctionsPanel>(cx))
            .unwrap()
    }

    /// Returns the hand-built sample program, a caller and its callee, as a loaded binary.
    pub(crate) fn sample() -> Arc<LoadedBinary> {
        let (program, analysis, overlay) = crate::code_view::tests::sample_program();
        loaded_of(program, analysis, overlay)
    }

    /// Returns `program`, its `analysis` and `overlay` as a loaded binary, its function rows
    /// read as a load reads them.
    pub(crate) fn loaded_of(
        program: borer_engine::program::Program,
        analysis: borer_engine::analysis::Analysis,
        overlay: borer_engine::analysis::Overlay,
    ) -> Arc<LoadedBinary> {
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
            fingerprint: overlay.fingerprint(),
            overlay: Arc::new(overlay),
            initial_rows,
            notes: Vec::new(),
            identity: String::new(),
        })
    }

    /// Returns the window's binary, which `workspace`'s status line holds.
    ///
    /// # Panics
    ///
    /// Panics if the workspace has no status line.
    pub(crate) fn binary_in(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Entity<Binary> {
        workspace.read_with(cx, |workspace, cx| {
            let line = workspace.status_bar().read(cx).item_of_type::<StatusLine>();
            line.unwrap().read(cx).binary().clone()
        })
    }

    /// Opens `place` of `loaded` in `workspace` as `mode` says, focused, through
    /// [`open`](crate::places::open) with the window's binary, which the status line holds.
    ///
    /// # Panics
    ///
    /// Panics if the workspace has no status line.
    pub(crate) fn open_place(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        place: Place,
        mode: TabMode,
        cx: &mut VisualTestContext,
    ) {
        let binary = binary_in(workspace, cx);
        workspace.update_in(cx, |workspace, window, cx| {
            let how = Opening { mode, focus: true };
            places::open(workspace, &binary, loaded, place, how, window, cx);
        });
    }

    /// Opens the sample's caller in `workspace`'s active pane as `mode` says, focused.
    pub(crate) fn open_caller(
        workspace: &Entity<Workspace>,
        mode: TabMode,
        cx: &mut VisualTestContext,
    ) {
        open_place(workspace, &sample(), Place::decompile(CALLER), mode, cx);
    }

    /// Returns the function and top line of the active decompile tab, once the work settled
    /// and a frame laid the tab out.
    pub(crate) fn shown(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Option<(u64, usize)> {
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

    /// An open decompile tab moves to the state an edit leaves and shows the new name at
    /// once, and opening its function again finds that tab rather than adding one.
    ///
    /// # Panics
    ///
    /// Panics if the tab keeps the old state or name, or a second tab opens.
    #[gpui::test]
    fn an_open_tab_follows_an_edit(cx: &mut TestAppContext) {
        an_open_tab_follows_an_edit_steps(cx);
    }

    /// Runs the steps of [`an_open_tab_follows_an_edit`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`an_open_tab_follows_an_edit`] says.
    fn an_open_tab_follows_an_edit_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let dir = crate::worker::tests::scratch("follow");
        let exe = dir.join("tiny.exe");
        std::fs::write(&exe, crate::worker::tests::tiny_pe()).unwrap();
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let binary = binary_in(&workspace, cx);
        binary.update(cx, |binary, cx| binary.open_path(exe, cx));
        cx.run_until_parked();
        let helper = crate::worker::tests::HELPER;
        let show = |cx: &mut VisualTestContext| {
            let now = binary.read_with(cx, |binary, _| binary.loaded().cloned().unwrap());
            open_place(
                &workspace,
                &now,
                Place::decompile(helper),
                TabMode::Permanent,
                cx,
            );
            cx.run_until_parked();
            now
        };
        show(cx);
        let rename = borer_engine::analysis::edit::Edit::Name {
            at: helper,
            name: "renamed_helper".to_owned(),
        };
        binary.update(cx, |binary, cx| binary.edit(vec![rename], cx));
        cx.run_until_parked();
        let now = show(cx);
        std::fs::remove_dir_all(&dir).unwrap();
        let tabs: Vec<Entity<DecompileItem>> = workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            pane.items_of_type::<DecompileItem>()
                .filter(|tab| tab.read(cx).entry() == Some(helper))
                .collect()
        });
        assert_eq!(tabs.len(), 1);
        let (moved, text) = tabs[0].read_with(cx, |tab, _| {
            let first = tab.code().and_then(|code| code.get(0));
            (
                Arc::ptr_eq(tab.loaded(), &now),
                first.map(|(view, _)| view.spell()),
            )
        });
        assert!(moved);
        let text = text.unwrap_or_default();
        assert!(text.contains("renamed_helper"), "{text}");
    }

    /// Returns the window's binary with the sample open, a decompile tab of the caller and
    /// its listing opened at its fourth instruction, both drawn and settled.
    ///
    /// # Returns
    ///
    /// The binary, and the listing's top line.
    ///
    /// # Panics
    ///
    /// Panics if the panel is gone.
    fn two_code_tabs(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> (Entity<Binary>, usize) {
        let binary = binary_in(workspace, cx);
        let loaded = sample();
        binary.update(cx, |binary, cx| {
            binary.finish_load(Ok(loaded.clone()), cx);
        });
        let (va, line) = crate::decompile_item::tests::fourth_instruction(&loaded);
        let listing = Place::Code {
            entry: CALLER,
            form: Form::Listing,
            at: Some(va),
        };
        for place in [Place::decompile(CALLER), listing] {
            open_place(workspace, &loaded, place, TabMode::Permanent, cx);
            shown(workspace, cx);
        }
        (binary, line)
    }

    /// Renames the sample's callee to `name` through the edit path and waits for every
    /// view to settle.
    fn rename_callee(binary: &Entity<Binary>, name: &str, cx: &mut VisualTestContext) {
        let rename = borer_engine::analysis::edit::Edit::Name {
            at: CALLEE,
            name: name.to_owned(),
        };
        binary.update(cx, |binary, cx| binary.edit(vec![rename], cx));
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        cx.run_until_parked();
    }

    /// An edit builds every code tab again under the new name, through the tab's own
    /// following of the binary, with the line at its top kept.
    ///
    /// # Panics
    ///
    /// Panics if a tab keeps the old name or moves off its line.
    #[gpui::test]
    fn an_edit_rebuilds_each_code_tab_at_its_line(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let (binary, line) = two_code_tabs(&workspace, cx);
        rename_callee(&binary, "renamed_callee", cx);
        let tabs = workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            pane.items_of_type::<DecompileItem>()
                .map(|tab| {
                    let tab = tab.read(cx);
                    let text = tab.code().and_then(|code| code.get(0));
                    let text = text.map(|(view, _)| view.spell()).unwrap_or_default();
                    (tab.form(), tab.top_line(), text)
                })
                .collect::<Vec<_>>()
        });
        assert_eq!(tabs.len(), 2);
        for (form, top, text) in tabs {
            let want = if form == Form::Listing { line } else { 0 };
            assert_eq!(top, want, "{form:?}");
            assert!(text.contains("renamed_callee"), "{form:?}: {text}");
        }
    }

    /// After an edit settles, every open view shows the state the edit left: each reports
    /// the binary's overlay fingerprint, named by its type when it does not.
    ///
    /// # Panics
    ///
    /// Panics naming the first view left on an older state.
    #[gpui::test]
    fn no_view_is_left_on_an_old_revision_after_an_edit(cx: &mut TestAppContext) {
        use crate::binary::Revision as _;
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let (binary, _) = two_code_tabs(&workspace, cx);
        rename_callee(&binary, "renamed_callee", cx);
        let now = binary.read_with(cx, |binary, _| binary.loaded().map(|l| l.fingerprint));
        let views = workspace.read_with(cx, |workspace, cx| {
            let panel = workspace.panel::<FunctionsPanel>(cx).unwrap();
            let mut views = vec![("FunctionsPanel", panel.read(cx).revision())];
            for pane in workspace.panes() {
                for tab in pane.read(cx).items_of_type::<DecompileItem>() {
                    views.push(("DecompileItem", tab.read(cx).revision()));
                }
            }
            views
        });
        assert_eq!(views.len(), 3);
        for (view, revision) in views {
            assert_eq!(revision, now, "{view} is left on an old revision");
        }
    }

    /// Every action of the `borer` namespace is available to Zed's command palette: every
    /// window-wide one with the functions panel focused and with a decompile tab focused,
    /// and every one with the call tree focused, whose own actions it answers itself.
    ///
    /// # Panics
    ///
    /// Panics if an action is missing in any of those places.
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
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        load_sample(&app, cx);
        let declared: Vec<&str> = cx.update(|_, cx| {
            cx.all_action_names()
                .iter()
                .copied()
                .filter(|name| name.starts_with("borer::"))
                .collect()
        });
        assert!(!declared.is_empty());
        let own: Vec<&str> = OWN_ACTIONS.iter().map(|action| action.name()).collect();
        assert!(own.iter().all(|name| declared.contains(name)));
        let wide: Vec<&str> = declared
            .iter()
            .copied()
            .filter(|name| !own.contains(name))
            .collect();
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        assert_available(&wide, cx);
        open_caller(&workspace, TabMode::Permanent, cx);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), Some(CALLER));
        assert_available(&wide, cx);
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<CallTreePanel>(window, cx);
        });
        assert_available(&declared, cx);
    }

    /// The X11 window icon is the embedded 128 px app icon, decoded.
    ///
    /// # Panics
    ///
    /// Panics if the icon does not decode to 128 by 128 pixels.
    #[test]
    fn window_icon_decodes() {
        let icon = window_icon().unwrap();
        assert_eq!(icon.dimensions(), (128, 128));
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
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        load_sample(&app, cx);
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

    /// The function table shows its brief columns until the palette's
    /// [`ToggleFunctionColumns`] shows them all, and takes them away again.
    ///
    /// # Panics
    ///
    /// Panics if the table starts with other columns or the action does not toggle them.
    #[gpui::test]
    fn the_palette_toggles_the_function_columns(cx: &mut TestAppContext) {
        the_palette_toggles_the_function_columns_steps(cx);
    }

    /// Runs the steps of [`the_palette_toggles_the_function_columns`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_palette_toggles_the_function_columns`] says.
    fn the_palette_toggles_the_function_columns_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let panel = load_sample(&app, cx);
        app.workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        for columns in [Columns::Brief, Columns::Full, Columns::Brief] {
            assert_eq!(panel.read_with(cx, |panel, _| panel.columns()), columns);
            cx.dispatch_action(ToggleFunctionColumns);
            cx.run_until_parked();
        }
    }

    /// A decompile tab is titled by the engine's name of its function once the decompile
    /// is in, and carries the code icon; a tab the engine decompiled nothing for keeps its
    /// entry as its title.
    ///
    /// # Panics
    ///
    /// Panics if a title is not the engine's name or the entry, or the tab has no icon.
    #[gpui::test]
    fn a_decompile_tab_is_titled_by_its_function(cx: &mut TestAppContext) {
        a_decompile_tab_is_titled_by_its_function_steps(cx);
    }

    /// Runs the steps of [`a_decompile_tab_is_titled_by_its_function`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_decompile_tab_is_titled_by_its_function`] says.
    fn a_decompile_tab_is_titled_by_its_function_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        open_caller(&workspace, TabMode::Permanent, cx);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), Some(CALLER));
        let loaded = sample();
        let name = name_of(&loaded.analysis, &loaded.overlay, CALLER);
        let (title, icon) = cx.update(|window, cx| {
            let item = workspace.read(cx).active_item(cx).unwrap();
            (item.tab_content_text(0, cx), item.tab_icon(window, cx))
        });
        assert_eq!(title, name);
        assert!(icon.is_some());
        let nowhere = 0x5;
        open_place(
            &workspace,
            &loaded,
            Place::decompile(nowhere),
            TabMode::Permanent,
            cx,
        );
        assert_eq!(shown(&workspace, cx), Some((nowhere, 0)));
        let (title, decompiled) = cx.update(|_, cx| {
            let item = workspace
                .read(cx)
                .active_item_as::<DecompileItem>(cx)
                .unwrap();
            let item = item.read(cx);
            (item.tab_content_text(0, cx), item.code().is_some())
        });
        assert_eq!(title, "0x5");
        assert!(!decompiled);
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
        let dir = folder_with_settings(&app_state, "drop-test").await;
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        drop_on_center(&dir, cx);
        assert!(take_status(&app, cx).ends_with(REFUSED_FOLDER));
        open_caller(&workspace, TabMode::Permanent, cx);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), Some(CALLER));
        drop_on_center(&dir, cx);
        assert!(take_status(&app, cx).ends_with(REFUSED_FOLDER));
        cx.dispatch_action(AddFolderToProject);
        cx.run_until_parked();
        cx.simulate_path_prompt_response(|_| Some(vec![dir.clone()]));
        cx.run_until_parked();
        assert!(take_status(&app, cx).starts_with("load failed"));
        std::fs::remove_dir_all(&dir).unwrap();
        let folders = workspace.read_with(cx, |workspace, cx| {
            workspace.project().read(cx).worktrees(cx).count()
        });
        assert_eq!(folders, 0);
        assert!(cx.update(|_, cx| DisableAiSettings::get_global(cx).disable_ai));
    }

    /// Returns a new folder `borer-app-<name>-<pid>` under the temporary directory, whose
    /// `.zed/settings.json` would start a context server if Zed read it.
    ///
    /// # Panics
    ///
    /// Panics if the folder cannot be made.
    pub(crate) async fn folder_with_settings(app_state: &Arc<AppState>, name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("borer-app-{name}-{}", std::process::id()));
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
        dir
    }

    /// A panel docked after a load lists the open binary and opens its first function.
    ///
    /// # Panics
    ///
    /// Panics if the late panel shows no rows or opens nothing.
    #[gpui::test]
    fn the_panel_follows_what_is_open_not_what_was_sent(cx: &mut TestAppContext) {
        the_panel_follows_what_is_open_not_what_was_sent_steps(cx);
    }

    /// Runs the steps of [`the_panel_follows_what_is_open_not_what_was_sent`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_panel_follows_what_is_open_not_what_was_sent`]
    /// says.
    fn the_panel_follows_what_is_open_not_what_was_sent_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let loaded = sample();
        app.binary
            .update(cx, |binary, cx| binary.finish_load(Ok(loaded.clone()), cx));
        cx.run_until_parked();
        let workspace = app.workspace;
        let panel = workspace.read_with(cx, |workspace, cx| workspace.panel::<FunctionsPanel>(cx));
        let panel = panel.unwrap();
        panel.update_in(cx, |panel, window, cx| panel.follow(window, cx));
        cx.run_until_parked();
        assert_eq!(panel.read_with(cx, |panel, cx| panel.empty(cx)), None);
        let first = loaded.initial_rows.rows.first().map(|row| row.entry);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), first);
    }

    /// A load that starts in the update another finished in leaves no tab of the first.
    ///
    /// # Panics
    ///
    /// Panics if a tab of the closed load opens.
    #[gpui::test]
    fn a_load_closed_in_its_update_opens_no_tab(cx: &mut TestAppContext) {
        a_load_closed_in_its_update_opens_no_tab_steps(cx);
    }

    /// Runs the steps of [`a_load_closed_in_its_update_opens_no_tab`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_load_closed_in_its_update_opens_no_tab`] says.
    fn a_load_closed_in_its_update_opens_no_tab_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let (workspace, binary) = (app.workspace, app.binary);
        let missing = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        binary.update(cx, |binary, cx| {
            binary.finish_load(Ok(sample()), cx);
            binary.open_path(missing, cx);
        });
        cx.run_until_parked();
        let tab = workspace.read_with(cx, |workspace, cx| {
            workspace.active_item_as::<DecompileItem>(cx).is_some()
        });
        assert!(!tab, "a tab of the closed load opened");
    }

    /// Open asks for a file with no functions panel docked.
    ///
    /// # Panics
    ///
    /// Panics if no path prompt appears.
    #[gpui::test]
    fn open_works_with_no_panel_docked(cx: &mut TestAppContext) {
        open_works_with_no_panel_docked_steps(cx);
    }

    /// Runs the steps of [`open_works_with_no_panel_docked`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`open_works_with_no_panel_docked`] says.
    fn open_works_with_no_panel_docked_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (_, cx) = open(&app_state, cx);
        cx.dispatch_action(Open);
        cx.run_until_parked();
        assert!(cx.did_prompt_for_paths());
    }

    /// A file dropped on the start tab starts the window's binary reading it with no
    /// functions panel docked.
    ///
    /// # Panics
    ///
    /// Panics if the binary never tried to load the file.
    #[gpui::test]
    fn a_dropped_file_opens_with_no_panel_docked(cx: &mut TestAppContext) {
        a_dropped_file_opens_with_no_panel_docked_steps(cx);
    }

    /// Runs the steps of [`a_dropped_file_opens_with_no_panel_docked`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_dropped_file_opens_with_no_panel_docked`] says.
    fn a_dropped_file_opens_with_no_panel_docked_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let binary = app.binary;
        let file = std::env::temp_dir().join("borer-app-no-such-dropped.exe");
        drop_on_center(&file, cx);
        let failed = binary.read_with(cx, |binary, _| binary.load_error().map(str::to_owned));
        assert!(failed.is_some(), "the drop started no load");
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
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
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
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
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

    /// A saved layout that does not parse says so in the status line and leaves the default
    /// layout: the panel opens on the left with the first load.
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
        let (app, cx) = open(&app_state, cx);
        assert!(take_status(&app, cx).starts_with("dock layout not restored"));
        load_sample(&app, cx);
        assert!(app.workspace.read_with(cx, |workspace, cx| {
            let dock = workspace.left_dock().read(cx);
            dock.is_open() && dock.panel::<FunctionsPanel>().is_some()
        }));
    }

    /// The functions panel moved to the right dock comes back open there with the first load
    /// in a new workspace over the same database.
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
            let (app, cx) = open(&app_state, cx);
            let workspace = app.workspace.clone();
            let panel = load_sample(&app, cx);
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
        let (app, cx) = open(&app_state, cx);
        load_sample(&app, cx);
        assert!(
            app.workspace
                .read_with(cx, |workspace, cx| in_open_right_dock(workspace, cx))
        );
    }

    /// The functions panel's width and its dock's visibility, saved through Zed's
    /// persistence, come back with the first load in a new workspace over the same database.
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
            let (app, cx) = open(&app_state, cx);
            let workspace = app.workspace.clone();
            load_sample(&app, cx);
            let open_at_load =
                workspace.read_with(cx, |workspace, cx| workspace.left_dock().read(cx).is_open());
            assert!(open_at_load);
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
        let (app, cx) = open(&app_state, cx);
        load_sample(&app, cx);
        app.workspace.read_with(cx, |workspace, cx| {
            let saved = workspace.panel_size_state::<FunctionsPanel>(cx);
            assert_eq!(saved.and_then(|state| state.size), Some(width));
            assert!(!workspace.left_dock().read(cx).is_open());
        });
    }

    /// Before a load nothing is docked, no dock is open, the center holds only the start
    /// tab and draws no tab bar over it; the first load docks the functions panel, opens
    /// it, and opens the first function in a tab under a tab bar.
    ///
    /// # Panics
    ///
    /// Panics if a panel or a tab bar shows before the load, or the load docks nothing.
    #[gpui::test]
    fn nothing_is_docked_until_a_binary_loads(cx: &mut TestAppContext) {
        nothing_is_docked_until_a_binary_loads_steps(cx);
    }

    /// Runs the steps of [`nothing_is_docked_until_a_binary_loads`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`nothing_is_docked_until_a_binary_loads`] says.
    fn nothing_is_docked_until_a_binary_loads_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        app.workspace.read_with(cx, |workspace, cx| {
            assert!(workspace.panel::<FunctionsPanel>(cx).is_none());
            for dock in [
                workspace.left_dock(),
                workspace.bottom_dock(),
                workspace.right_dock(),
            ] {
                assert!(!dock.read(cx).is_open());
            }
            let pane = workspace.active_pane().read(cx);
            assert_eq!(pane.items_len(), 1);
            assert!(workspace.active_item_as::<StartItem>(cx).is_some());
        });
        let start = cx.debug_bounds("start-item").unwrap();
        let title = cx.debug_bounds("title-bar").unwrap();
        assert!(
            start.origin.y - title.bottom() < px(4.0),
            "a tab bar sits over the start tab"
        );
        load_sample(&app, cx);
        assert_eq!(
            shown(&app.workspace, cx).map(|(entry, _)| entry),
            Some(CALLER)
        );
        app.workspace.read_with(cx, |workspace, cx| {
            let dock = workspace.left_dock().read(cx);
            assert!(dock.is_open() && dock.panel::<FunctionsPanel>().is_some());
            assert!(workspace.active_item_as::<StartItem>(cx).is_none());
        });
    }

    /// A load puts the binary first among those opened before, under its absolute path and
    /// with the engine's architecture and format, and the list comes back in a new window
    /// over the same database.
    ///
    /// # Panics
    ///
    /// Panics if the list misses the binary or does not come back.
    #[gpui::test]
    fn a_loaded_binary_is_remembered_for_the_start_tab(cx: &mut TestAppContext) {
        a_loaded_binary_is_remembered_for_the_start_tab_steps(cx);
    }

    /// Runs the steps of [`a_loaded_binary_is_remembered_for_the_start_tab`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_loaded_binary_is_remembered_for_the_start_tab`]
    /// says.
    fn a_loaded_binary_is_remembered_for_the_start_tab_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let want = {
            let (app, cx) = open(&app_state, cx);
            assert!(
                app.binary
                    .read_with(cx, |binary, _| binary.recent().is_empty())
            );
            load_sample(&app, cx);
            let recent = app
                .binary
                .read_with(cx, |binary, _| binary.recent().to_vec());
            assert_eq!(recent.len(), 1);
            let given = PathBuf::from("sample.bin");
            assert_eq!(recent[0].path, std::path::absolute(&given).unwrap());
            assert!(recent[0].path.is_absolute());
            assert!(!recent[0].kind.is_empty());
            recent
        };
        cx.run_until_parked();
        let (app, cx) = open(&app_state, cx);
        let back = app
            .binary
            .read_with(cx, |binary, _| binary.recent().to_vec());
        assert_eq!(back, want);
    }

    /// A window opens titled `borer`, with the system's title bar hidden for the app's own,
    /// and stays hidden until its first frame, so it never shows empty.
    ///
    /// # Panics
    ///
    /// Panics if an option says otherwise.
    #[gpui::test]
    fn a_window_opens_hidden_under_the_apps_title_bar(cx: &mut TestAppContext) {
        a_window_opens_hidden_under_the_apps_title_bar_steps(cx);
    }

    /// Runs the steps of [`a_window_opens_hidden_under_the_apps_title_bar`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_window_opens_hidden_under_the_apps_title_bar`] says.
    fn a_window_opens_hidden_under_the_apps_title_bar_steps(cx: &mut TestAppContext) {
        init(cx);
        let options = cx.update(|cx| super::window_options(cx));
        assert!(!options.show);
        let titlebar = options.titlebar.unwrap();
        assert!(titlebar.appears_transparent);
        assert_eq!(titlebar.title.as_deref(), Some("borer"));
        assert!(options.window_min_size.is_some());
    }

    /// An app window opened hidden is shown and brought forward, so it is the active window.
    ///
    /// # Panics
    ///
    /// Panics if the window does not open or is not the active one.
    #[gpui::test]
    fn an_opened_window_is_shown_and_active(cx: &mut TestAppContext) {
        an_opened_window_is_shown_and_active_steps(cx);
    }

    /// Runs the steps of [`an_opened_window_is_shown_and_active`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`an_opened_window_is_shown_and_active`] says.
    fn an_opened_window_is_shown_and_active_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let window = cx
            .update(|cx| super::open_window(&app_state, None, cx))
            .unwrap();
        cx.run_until_parked();
        let active = cx.update(|cx| cx.active_window());
        assert_eq!(active, Some(window.into()));
    }
}
