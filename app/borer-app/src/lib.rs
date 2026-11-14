//! Desktop GPUI application over [`borer_engine`].

pub mod actions;
pub mod app_view;
pub mod code_view;
pub mod history;
pub mod palette;
pub mod theme_provider;
pub mod worker;

use std::io::Write as _;
use std::path::PathBuf;

use gpui::{App, AppContext as _, Bounds, WindowBounds, WindowOptions, px, size};
use theme::LoadThemes;

use crate::actions::bind_keys;
use crate::app_view::AppView;
use crate::theme_provider::AppThemeSettings;
use crate::worker::mark_ui_thread;

/// Default window width in logical pixels.
const WINDOW_WIDTH_PX: f32 = 1280.0;

/// Default window height in logical pixels.
const WINDOW_HEIGHT_PX: f32 = 800.0;

/// Boots the GPUI platform, registers base theme settings and key bindings, and opens [`AppView`].
///
/// # Errors
///
/// Returns an error if command-line arguments are invalid before launch.
pub fn run() -> anyhow::Result<()> {
    let initial_path = std::env::args_os().nth(1).map(PathBuf::from);
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
        if let Err(err) = cx.open_window(options, move |window, cx| {
            cx.new(|cx| AppView::new(initial_path, window, cx))
        }) {
            let _ = writeln!(std::io::stderr().lock(), "borer-app: {err:#}");
            cx.quit();
        }
    });
    Ok(())
}
