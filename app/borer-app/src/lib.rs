//! Desktop GPUI application over [`borer_engine`].

pub mod actions;
pub mod app_view;
pub mod code_view;
pub mod history;
pub mod measure;
pub mod theme_provider;
pub mod worker;

use gpui::{App, AppContext as _, Bounds, WindowBounds, WindowOptions, px, size};
use theme::LoadThemes;

use crate::actions::bind_keys;
use crate::app_view::AppView;
use crate::measure::{CliMode, new_cli_exit_slot, parse_cli_args, run_headless};
use crate::theme_provider::AppThemeSettings;
use crate::worker::mark_ui_thread;

/// Default window width in logical pixels.
const WINDOW_WIDTH_PX: f32 = 1280.0;

/// Default window height in logical pixels.
const WINDOW_HEIGHT_PX: f32 = 800.0;

/// Boots the GPUI platform (or `--headless` mode) according to CLI flags.
///
/// # Errors
///
/// Returns an error if CLI flags are invalid, opening the window fails, or a
/// non-interactive CLI mode (`--headless`, `--report-open`, `--measure-memory`,
/// `--measure`) fails to load or measure its target binary.
pub fn run() -> anyhow::Result<()> {
    let mode = parse_cli_args()?;
    if let CliMode::Headless(path) = mode {
        return run_headless(path);
    }
    let exit_slot = new_cli_exit_slot();
    let app_slot = exit_slot.clone();
    gpui_platform::application().run(move |cx: &mut App| {
        mark_ui_thread();
        theme::init(LoadThemes::JustBase, cx);
        theme::set_theme_settings_provider(Box::new(AppThemeSettings::new()), cx);
        bind_keys(cx);
        let bounds = Bounds::centered(None, size(px(WINDOW_WIDTH_PX), px(WINDOW_HEIGHT_PX)), cx);
        let options = WindowOptions {
            window_bounds: Some(WindowBounds::Windowed(bounds)),
            ..WindowOptions::default()
        };
        let view_slot = app_slot.clone();
        if let Err(err) = cx.open_window(options, move |window, cx| {
            cx.new(|cx| AppView::new_with_mode(mode, view_slot, window, cx))
        }) {
            *app_slot.borrow_mut() = Some(err);
            cx.quit();
        }
    });
    if let Some(err) = exit_slot.borrow_mut().take() {
        return Err(err);
    }
    Ok(())
}
