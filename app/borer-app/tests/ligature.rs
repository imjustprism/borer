//! With the app's fonts and its buffer font, `!=`, `->` and `==` each shape to the two
//! glyphs their characters shape to alone: no ligature.
//!
//! Lilex keeps two glyphs when its ligatures are on and swaps both for joined halves, so the
//! glyphs are compared, not counted. Windows' headless platform shapes nothing, so there the
//! test takes the windowed one; `!` and `=` shaping apart proves the shaper is real. The
//! shaper comes from the real platform, which macOS builds only on the main thread, so this
//! target has no test harness and runs the test from `main`.

#![expect(
    clippy::expect_used,
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use gpui::{AssetSource as _, TestAppContext, TestDispatcher, TextRun, WindowTextSystem};
use settings::Settings as _;
use theme_settings::ThemeSettings;

mod support;

use support::boot;

/// Runs the test on the main thread.
fn main() {
    the_buffer_font_draws_no_ligature();
}

/// Shapes each operator alone and as a pair and asserts the pair has the glyphs of its parts.
fn the_buffer_font_draws_no_ligature() {
    let text_system = gpui_platform::current_platform(cfg!(not(windows))).text_system();
    let cx = TestAppContext::build_with_text_system(TestDispatcher::new(0), None, text_system);
    cx.update(|cx| {
        boot(cx);
        let fonts = assets::Assets
            .list("fonts")
            .expect("the bundled fonts list")
            .into_iter()
            .filter(|path| path.ends_with(".ttf"))
            .map(|path| {
                assets::Assets
                    .load(&path)
                    .expect("loads")
                    .expect("is there")
            })
            .collect();
        cx.text_system().add_fonts(fonts).expect("the fonts load");
        let settings = ThemeSettings::get_global(cx);
        let (font, size) = (settings.buffer_font.clone(), settings.buffer_font_size(cx));
        let shaper = WindowTextSystem::new(cx.text_system().clone());
        let glyphs = |text: &str| {
            let run = TextRun {
                len: text.len(),
                font: font.clone(),
                color: gpui::black(),
                background_color: None,
                underline: None,
                strikethrough: None,
            };
            let line = shaper.layout_line(text, size, &[run], None);
            let ids = line.runs.iter().flat_map(|run| run.glyphs.iter());
            ids.map(|glyph| glyph.id).collect::<Vec<_>>()
        };
        for pair in ["!=", "->", "=="] {
            let alone: Vec<_> = pair.chars().flat_map(|c| glyphs(&c.to_string())).collect();
            assert_eq!(alone.len(), 2, "{pair}");
            assert!(
                pair == "==" || alone[0] != alone[1],
                "{pair}: the shaper is a stand-in"
            );
            assert_eq!(glyphs(pair), alone, "{pair} shapes as a ligature");
        }
    });
}
