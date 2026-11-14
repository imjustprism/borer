//! Desktop GPUI application over [`borer_engine`].

pub mod theme_provider;

use std::io::Write as _;

use gpui::{
    App, AppContext as _, Bounds, Context, IntoElement, ParentElement as _, Render, Styled as _,
    Window, WindowBounds, WindowOptions, div, px, size,
};
use theme::{ActiveTheme as _, LoadThemes};
use ui::Label;

use crate::theme_provider::AppThemeSettings;

/// Default window width in logical pixels.
const WINDOW_WIDTH_PX: f32 = 1280.0;

/// Default window height in logical pixels.
const WINDOW_HEIGHT_PX: f32 = 800.0;

/// Placeholder root view opened by the initial workspace commit.
#[derive(Debug)]
struct BootView {
    /// Engine version label confirming the workspace links [`borer_engine`].
    status: &'static str,
}

impl Render for BootView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let _ = borer_engine::analysis::EnumSource::Binary;
        let colors = cx.theme().colors();
        div()
            .size_full()
            .bg(colors.background)
            .text_color(colors.text)
            .p(px(12.0))
            .child(Label::new(self.status))
    }
}

/// Boots the GPUI platform, registers base theme settings, and opens the main window.
///
/// # Errors
///
/// Returns an error only when diagnostic output fails before entering the event loop.
pub fn run() -> anyhow::Result<()> {
    gpui_platform::application().run(|cx: &mut App| {
        theme::init(LoadThemes::JustBase, cx);
        theme::set_theme_settings_provider(Box::new(AppThemeSettings::new()), cx);
        let bounds = Bounds::centered(None, size(px(WINDOW_WIDTH_PX), px(WINDOW_HEIGHT_PX)), cx);
        let options = WindowOptions {
            window_bounds: Some(WindowBounds::Windowed(bounds)),
            ..WindowOptions::default()
        };
        if let Err(err) = cx.open_window(options, |_, cx| {
            cx.new(|_| BootView {
                status: "borer-app ready",
            })
        }) {
            let _ = writeln!(std::io::stderr().lock(), "borer-app: {err:#}");
            cx.quit();
        }
    });
    Ok(())
}
