//! The window's title bar, drawn by the app over the full width of the window: the mark,
//! the menu bar, the open binary's name, and the window controls.
//!
//! Zed's [`PlatformTitleBar`] gives the drag area, the double click, the caption buttons
//! of Windows (hit-tested by the platform through their `WindowControlArea`), the controls
//! of Linux client-side decorations and the room macOS keeps for its traffic lights; the
//! app fills it with its own children.

use gpui::{
    AnyElement, App, AppContext as _, Context, Entity, Hsla, InteractiveElement as _, IntoElement,
    ParentElement as _, Render, StatefulInteractiveElement as _, Styled as _, Subscription, Window,
    div, px, svg,
};
use platform_title_bar::PlatformTitleBar;
use theme::{ActiveTheme as _, ThemeColors};
use ui::{Color, Tooltip, h_flex};

use crate::app_assets::MARK_PATH;
use crate::binary::Binary;
use crate::menus::MenuBar;
use crate::start_item::small;

/// Width in logical pixels of the cell the mark sits in, the rail's width below it.
pub const MARK_CELL_PX: f32 = 40.0;

/// Side in logical pixels of the mark in the title bar.
const MARK_PX: f32 = 19.0;

/// Window width in logical pixels from which the binary's folder follows its name.
const FOLDER_SHOWN_FROM_PX: f32 = 1000.0;

/// Returns the color the caption buttons of Windows draw their glyphs in at rest: the
/// theme's muted text.
///
/// Zed's caption buttons set no color of their own at rest and inherit the title bar's;
/// hovered, minimize and maximize take the theme's `text` over `ghost_element_hover`, and
/// close the white-on-red of Windows.
///
/// # Arguments
///
/// * `colors` - The active theme's colors.
#[must_use]
pub const fn caption_glyph(colors: &ThemeColors) -> Hsla {
    colors.text_muted
}

/// What the title bar and the window's title call the open binary: its title
/// ([`Binary::title`]) and its folder, `borer` and no folder with nothing open.
///
/// # Arguments
///
/// * `binary` - The window's binary.
/// * `cx` - Application context reading it.
#[must_use]
pub fn binary_title(binary: &Entity<Binary>, cx: &App) -> (String, Option<String>) {
    let Some(loaded) = binary.read(cx).loaded() else {
        return (String::from("borer"), None);
    };
    let path = &loaded.path;
    let name = binary.read(cx).title();
    let folder = path.parent().map(|dir| dir.display().to_string());
    (name, folder.filter(|folder| !folder.is_empty()))
}

/// The title bar: the mark over the rail, the menus, the binary's name centered.
pub struct TitleBar {
    /// Zed's platform title bar the children go in.
    platform: Entity<PlatformTitleBar>,
    /// The menu bar, drawn on Windows and Linux.
    menu_bar: Entity<MenuBar>,
    /// The window's binary, whose name the bar shows.
    binary: Entity<Binary>,
    /// Redraws the name and retitles the window when the binary changes.
    _observe: Subscription,
}

impl std::fmt::Debug for TitleBar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TitleBar").finish_non_exhaustive()
    }
}

impl TitleBar {
    /// Returns the title bar over `binary`, and titles the window after it.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary.
    /// * `window` - The window.
    /// * `cx` - Title bar context.
    #[must_use]
    pub fn new(binary: Entity<Binary>, window: &mut Window, cx: &mut Context<'_, Self>) -> Self {
        let observe = cx.observe_in(&binary, window, |bar: &mut Self, _, window, cx| {
            bar.retitle(window, cx);
            cx.notify();
        });
        let bar = Self {
            platform: cx.new(|cx| PlatformTitleBar::new("title-bar", cx)),
            menu_bar: cx.new(|_| MenuBar::new(binary.clone())),
            binary,
            _observe: observe,
        };
        bar.retitle(window, cx);
        bar
    }

    /// Returns the menu bar.
    #[must_use]
    pub const fn menu_bar(&self) -> &Entity<MenuBar> {
        &self.menu_bar
    }

    /// Titles the window after the open binary's file name, `borer` with none open.
    ///
    /// # Arguments
    ///
    /// * `window` - The window.
    /// * `cx` - Application context reading the binary.
    fn retitle(&self, window: &mut Window, cx: &App) {
        let (name, _) = binary_title(&self.binary, cx);
        window.set_window_title(&name);
    }

    /// Returns the mark's cell, as wide as the rail; a click opens the command palette.
    ///
    /// # Arguments
    ///
    /// * `cx` - Title bar context.
    fn render_mark(cx: &mut Context<'_, Self>) -> AnyElement {
        let hover = cx.theme().colors().ghost_element_hover;
        let soft = cx.theme().colors().text_muted;
        let palette = zed_actions::command_palette::Toggle;
        div()
            .id("title-mark")
            .occlude()
            .w(px(MARK_CELL_PX))
            .h_full()
            .flex_none()
            .flex()
            .items_center()
            .justify_center()
            .cursor_pointer()
            .hover(move |cell| cell.bg(hover))
            .tooltip(Tooltip::for_action_title("Command Palette", &palette))
            .on_click(|_, window, cx| {
                window.dispatch_action(Box::new(zed_actions::command_palette::Toggle), cx);
            })
            .child(svg().path(MARK_PATH).size(px(MARK_PX)).text_color(soft))
            .into_any_element()
    }

    /// Returns the binary's name, then its folder when the window is wide.
    ///
    /// # Arguments
    ///
    /// * `window` - The window, for its width.
    /// * `cx` - Title bar context.
    fn render_name(&self, window: &Window, cx: &App) -> AnyElement {
        let (name, folder) = binary_title(&self.binary, cx);
        let wide = window.viewport_size().width >= px(FOLDER_SHOWN_FROM_PX);
        h_flex()
            .gap(px(8.0))
            .child(small(name, Color::Muted))
            .children(
                folder
                    .filter(|_| wide)
                    .map(|folder| small(folder, Color::Placeholder)),
            )
            .into_any_element()
    }
}

impl Render for TitleBar {
    fn render(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let left = h_flex()
            .flex_1()
            .h_full()
            .child(Self::render_mark(cx))
            .child(self.menu_bar.clone())
            .into_any_element();
        let name = self.render_name(window, cx);
        let right = div().flex_1().into_any_element();
        self.platform
            .update(cx, |platform, _| platform.set_children([left, name, right]));
        div()
            .debug_selector(|| "title-bar".to_owned())
            .border_b_1()
            .border_color(cx.theme().colors().border)
            .text_color(caption_glyph(cx.theme().colors()))
            .child(self.platform.clone())
    }
}

#[cfg(test)]
mod tests {
    use gpui::TestAppContext;

    use super::{binary_title, caption_glyph};
    use crate::app_settings::BORER_THEME;
    use crate::app_view::tests::{init, load_sample, open};
    use crate::theme_contract::{QUIET_FLOOR, contrast};

    /// In each of borer's themes the caption glyphs read on the title bar at rest and on the
    /// hover fill Zed gives minimize and maximize.
    ///
    /// # Panics
    ///
    /// Panics if a glyph falls under [`QUIET_FLOOR`] on either fill.
    #[test]
    fn the_caption_glyphs_read_on_the_title_bar() {
        let family = theme_settings::deserialize_user_theme(BORER_THEME).unwrap();
        for content in &family.themes {
            let theme = theme_settings::refine_theme(content);
            let colors = theme.colors();
            let rest = contrast(caption_glyph(colors), colors.title_bar_background);
            assert!(rest >= QUIET_FLOOR, "{}: {rest:.2} at rest", theme.name);
            let hover = contrast(colors.text, colors.ghost_element_hover);
            assert!(hover >= QUIET_FLOOR, "{}: {hover:.2} hovered", theme.name);
        }
    }

    /// The title says `borer` with nothing open and the binary's file name once one loads;
    /// the sample's path has no folder, so none follows.
    ///
    /// # Panics
    ///
    /// Panics if the title says anything else.
    #[gpui::test]
    fn the_title_follows_the_binary(cx: &mut TestAppContext) {
        the_title_follows_the_binary_steps(cx);
    }

    /// Runs the steps of [`the_title_follows_the_binary`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_title_follows_the_binary`] says.
    fn the_title_follows_the_binary_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let title =
            |cx: &mut gpui::VisualTestContext| cx.update(|_, cx| binary_title(&app.binary, cx));
        assert_eq!(title(cx), (String::from("borer"), None));
        load_sample(&app, cx);
        assert_eq!(title(cx), (String::from("sample.bin"), None));
    }
}
