//! System font and density settings for [`theme`] and [`ui`].

use gpui::{App, Font, FontFallbacks, Pixels, px};
use theme::{ThemeSettingsProvider, UiDensity};

/// Default font size in logical pixels for UI labels and code views.
pub const FONT_SIZE_PX: f32 = 13.0;

/// System-font settings registered globally for the application window.
#[derive(Debug)]
pub struct AppThemeSettings {
    /// Proportional system font used for tables and chrome.
    ui_font: Font,
    /// Monospace font used for addresses and decompiled code.
    buffer_font: Font,
}

impl Default for AppThemeSettings {
    fn default() -> Self {
        Self::new()
    }
}

impl AppThemeSettings {
    /// Creates system font settings using `.SystemUIFont` and `Cascadia Mono`
    /// falling back to `Consolas`.
    ///
    /// # Returns
    ///
    /// The initialized font settings.
    #[must_use]
    pub fn new() -> Self {
        let mut buffer_font = gpui::font("Cascadia Mono");
        buffer_font.fallbacks = Some(FontFallbacks::from_fonts(vec!["Consolas".to_owned()]));
        Self {
            ui_font: gpui::font(".SystemUIFont"),
            buffer_font,
        }
    }
}

impl ThemeSettingsProvider for AppThemeSettings {
    fn ui_font<'a>(&'a self, _cx: &'a App) -> &'a Font {
        &self.ui_font
    }

    fn buffer_font<'a>(&'a self, _cx: &'a App) -> &'a Font {
        &self.buffer_font
    }

    fn ui_font_size(&self, _cx: &App) -> Pixels {
        px(FONT_SIZE_PX)
    }

    fn buffer_font_size(&self, _cx: &App) -> Pixels {
        px(FONT_SIZE_PX)
    }

    fn ui_density(&self, _cx: &App) -> UiDensity {
        UiDensity::Default
    }
}
