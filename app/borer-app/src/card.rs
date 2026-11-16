//! One look for a surface with no content to show: what it says, in which tone, and the
//! commands it offers.

use gpui::{
    AnyElement, App, InteractiveElement as _, IntoElement, ParentElement as _, SharedString,
    Styled as _,
};
use settings::Settings as _;
use theme_settings::ThemeSettings;
use ui::{Color, Label, LabelCommon as _, v_flex};

use crate::actions::{Hint, hint_row};

/// Debug selector of a drawn card, whose laid-out bounds the tests read.
pub const CARD_SELECTOR: &str = "card";

/// How a card's first line reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tone {
    /// A state, not a fault: nothing loaded, a build running, nothing matching.
    Quiet,
    /// The engine or a load failed.
    Error,
}

impl Tone {
    /// Returns the color the first line draws in.
    const fn color(self) -> Color {
        match self {
            Self::Quiet => Color::Muted,
            Self::Error => Color::Error,
        }
    }
}

/// What a surface with no content says instead, in the view's words.
#[derive(Debug, Clone)]
pub struct Card {
    /// The words: the first line in the tone's color, any further lines muted.
    pub says: SharedString,
    /// How the first line reads.
    pub tone: Tone,
    /// The commands offered under the words, each drawn as its key and what it does.
    pub offers: &'static [Hint],
}

impl Card {
    /// Returns the card drawn centered in its box: its words, then its offers as key-hint
    /// rows from the keymap, in the UI font.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the theme, the settings and the keymap.
    #[must_use]
    pub fn render(&self, cx: &App) -> AnyElement {
        let (first, rest) = self.says.split_once('\n').unwrap_or((&self.says, ""));
        let rest = (!rest.is_empty()).then(|| Label::new(rest.to_owned()).color(Color::Muted));
        v_flex()
            .size_full()
            .items_center()
            .justify_center()
            .gap_2()
            .debug_selector(|| CARD_SELECTOR.to_owned())
            .font(ThemeSettings::get_global(cx).ui_font.clone())
            .child(Label::new(first.to_owned()).color(self.tone.color()))
            .children(rest)
            .children(self.offers.iter().map(|hint| hint_row(*hint, cx)))
            .into_any_element()
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use workspace::Workspace;
    use workspace::dock::DockPosition;

    use super::{CARD_SELECTOR, Tone};
    use crate::app_view::add_functions_panel;
    use crate::app_view::tests::{init, open, sample};
    use crate::decompile_item::{DecompileItem, TabMode, open_function};
    use crate::functions_panel::FunctionsPanel;

    /// Lays the window out without settling background work, and returns whether a card
    /// was drawn.
    fn drawn(cx: &mut VisualTestContext) -> bool {
        cx.update(|window, cx| window.draw(cx).clear(cx));
        cx.debug_bounds(CARD_SELECTOR).is_some()
    }

    /// Returns what the functions panel's card says and its tone.
    fn panel_card(workspace: &Entity<Workspace>, cx: &mut VisualTestContext) -> (String, Tone) {
        workspace.read_with(cx, |workspace, cx| {
            let panel = workspace.panel::<FunctionsPanel>(cx).unwrap();
            let card = panel.read(cx).empty(cx).unwrap().card();
            (card.says.to_string(), card.tone)
        })
    }

    /// Returns what the active code tab's card says and its tone.
    fn tab_card(workspace: &Entity<Workspace>, cx: &mut VisualTestContext) -> (String, Tone) {
        workspace.read_with(cx, |workspace, cx| {
            let item = workspace.active_item_as::<DecompileItem>(cx).unwrap();
            let card = item.read(cx).card().unwrap();
            (card.says.to_string(), card.tone)
        })
    }

    /// The functions panel with no binary, while reading and after a failed load, and a
    /// code tab while it builds and once its build failed, each draw one card with the
    /// words they showed before cards.
    #[gpui::test]
    fn every_state_without_content_is_one_card(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        cx.update(|window, cx| {
            add_functions_panel(&app.workspace, &app.binary, DockPosition::Left, window, cx);
        });
        let (workspace, binary) = (app.workspace, app.binary);
        assert!(drawn(cx));
        let quiet = |says: &str| (says.to_owned(), Tone::Quiet);
        assert_eq!(panel_card(&workspace, cx), quiet("No binary loaded"));
        let path = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        binary.update(cx, |binary, cx| binary.open_path(path, cx));
        assert!(drawn(cx));
        let reading = quiet("Reading borer-app-no-such-binary.exe");
        assert_eq!(panel_card(&workspace, cx), reading);
        cx.run_until_parked();
        assert!(drawn(cx));
        let (says, tone) = panel_card(&workspace, cx);
        assert!(says.starts_with("Load failed: "), "{says}");
        assert_eq!(tone, Tone::Error);

        let loaded = sample();
        workspace.update_in(cx, |workspace, window, cx| {
            let panel = workspace.panel::<FunctionsPanel>(cx).unwrap();
            let rows = loaded.initial_rows.clone();
            panel.update(cx, |panel, cx| panel.show(loaded.clone(), rows, window, cx));
            open_function(
                workspace,
                loaded.clone(),
                0x1,
                TabMode::Permanent,
                true,
                window,
                cx,
            );
        });
        assert!(drawn(cx));
        assert_eq!(tab_card(&workspace, cx), quiet("Decompiling..."));
        cx.run_until_parked();
        assert!(drawn(cx));
        let failed = "Decompile failed\nNo function starts at 0x1.".to_owned();
        assert_eq!(tab_card(&workspace, cx), (failed, Tone::Error));
    }
}
