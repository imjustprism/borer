//! The theme picker: Zed's picker over every registered theme.
//!
//! Moving the selection shows that theme, Enter keeps it in the person's settings file,
//! and leaving any other way puts back the theme shown before.
//!
//! It holds the few lines of Zed's `theme_selector` the app needs, not that crate: its
//! confirm writes one named theme into the person's settings file when the dark and light
//! pair lives in the app's layer under it, losing the pair, and its footer offers Zed's
//! extensions, which the app does not have.

use std::sync::Arc;

use gpui::{
    DismissEvent, Entity, EventEmitter, FocusHandle, Focusable, Task, UpdateGlobal as _, WeakEntity,
};
use picker::{Picker, PickerDelegate};
use settings::{Settings as _, SettingsStore};
use theme::{Appearance, SystemAppearance, ThemeMeta, ThemeRegistry};
use theme_settings::ThemeSettings;
use ui::prelude::*;
use ui::{ListItem, ListItemSpacing};
use workspace::{DismissDecision, ModalView, Workspace};

use crate::actions::{ImportTheme, SelectTheme};
use crate::app_settings::{ThemeChange, change_theme, choose_theme, save_settings};
use crate::binary::Binary;
use crate::commands;

/// Registers the theme commands on `workspace`, over the window's `binary`: the picker,
/// importing a theme file ([`crate::theme_import::prompt`]), and Zed's light-dark toggle.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    commands::register(
        workspace,
        binary,
        |workspace, _: &SelectTheme, window, cx| {
            toggle(workspace, window, cx);
        },
    );
    commands::register(workspace, binary, |_, _: &ImportTheme, window, cx| {
        crate::theme_import::prompt(window, cx);
    });
    commands::register(
        workspace,
        binary,
        |_, _: &zed_actions::theme::ToggleMode, _, cx| {
            change_theme(ThemeChange::Flip, cx);
        },
    );
}

/// Opens the theme picker over `workspace`, or closes the one open.
///
/// # Arguments
///
/// * `workspace` - The workspace the picker opens over.
/// * `window` - The workspace's window.
/// * `cx` - Workspace context.
pub fn toggle(workspace: &mut Workspace, window: &mut Window, cx: &mut Context<'_, Workspace>) {
    workspace.toggle_modal(window, cx, |window, cx| {
        let delegate = ThemeDelegate::new(cx.entity().downgrade(), cx);
        ThemePicker {
            picker: cx.new(|cx| Picker::uniform_list(delegate, window, cx)),
        }
    });
}

/// The theme picker's modal: Zed's picker over [`ThemeDelegate`].
#[derive(Debug)]
pub struct ThemePicker {
    /// The picker.
    picker: Entity<Picker<ThemeDelegate>>,
}

impl ThemePicker {
    /// Returns the picker inside the modal.
    #[must_use]
    pub const fn picker(&self) -> &Entity<Picker<ThemeDelegate>> {
        &self.picker
    }
}

impl EventEmitter<DismissEvent> for ThemePicker {}

impl Focusable for ThemePicker {
    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.picker.focus_handle(cx)
    }
}

impl Render for ThemePicker {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<'_, Self>) -> impl IntoElement {
        v_flex()
            .key_context("ThemePicker")
            .w(rems(34.))
            .child(self.picker.clone())
    }
}

impl ModalView for ThemePicker {
    fn on_before_dismiss(
        &mut self,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> DismissDecision {
        self.picker
            .update(cx, |picker, cx| picker.delegate.revert(cx));
        DismissDecision::Dismiss(true)
    }
}

/// The theme picker's list: every registered theme, dark ones first, each by name.
pub struct ThemeDelegate {
    /// Every registered theme, dark ones first, each by name.
    themes: Vec<ThemeMeta>,
    /// The themes the query matches, as indices into [`Self::themes`].
    matches: Vec<usize>,
    /// The selected match, an index into [`Self::matches`].
    selected: usize,
    /// The theme settings in force when the picker opened, put back unless a theme is kept.
    original: ThemeSettings,
    /// The name of the theme shown when the picker opened.
    original_name: SharedString,
    /// Whether a theme was kept or the original put back, so nothing is put back again.
    settled: bool,
    /// The modal, which a confirm or dismiss closes.
    modal: WeakEntity<ThemePicker>,
}

impl std::fmt::Debug for ThemeDelegate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ThemeDelegate")
            .field("themes", &self.themes)
            .field("matches", &self.matches)
            .field("selected", &self.selected)
            .finish_non_exhaustive()
    }
}

impl ThemeDelegate {
    /// Returns the list over every registered theme, the shown one selected.
    ///
    /// # Arguments
    ///
    /// * `modal` - The modal the list is in.
    /// * `cx` - Application context reading the registry and the settings.
    fn new(modal: WeakEntity<ThemePicker>, cx: &App) -> Self {
        let mut themes = ThemeRegistry::global(cx).list();
        themes.sort_by(|a, b| {
            let light = a.appearance.is_light().cmp(&b.appearance.is_light());
            light.then_with(|| a.name.cmp(&b.name))
        });
        let original_name = cx.theme().name.clone();
        let selected = themes
            .iter()
            .position(|meta| meta.name == original_name)
            .unwrap_or_default();
        Self {
            matches: (0..themes.len()).collect(),
            themes,
            selected,
            original: ThemeSettings::get_global(cx).clone(),
            original_name,
            settled: false,
            modal,
        }
    }

    /// Returns the selected theme, if any matches.
    fn selected_theme(&self) -> Option<&ThemeMeta> {
        self.themes.get(*self.matches.get(self.selected)?)
    }

    /// Shows the selected theme without saving it.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context.
    fn preview(&self, cx: &mut App) {
        let Some(meta) = self.selected_theme() else {
            return;
        };
        let system = SystemAppearance::global(cx).0;
        let mut shown = self.original.clone();
        shown.theme = choose_theme(&shown.theme, &meta.name, meta.appearance, system).into();
        SettingsStore::update_global(cx, |store, _| store.override_global(shown));
    }

    /// Closes the modal the list is in.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context.
    fn close(&self, cx: &mut App) {
        if let Some(modal) = self.modal.upgrade() {
            modal.update(cx, |_, cx| cx.emit(DismissEvent));
        }
    }

    /// Puts back the theme settings in force when the picker opened, once.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context.
    fn revert(&mut self, cx: &mut App) {
        if !self.settled {
            self.settled = true;
            let original = self.original.clone();
            SettingsStore::update_global(cx, |store, _| store.override_global(original));
        }
    }
}

impl PickerDelegate for ThemeDelegate {
    type ListItem = ListItem;

    fn name() -> &'static str {
        "theme picker"
    }

    fn match_count(&self) -> usize {
        self.matches.len()
    }

    fn selected_index(&self) -> usize {
        self.selected
    }

    fn set_selected_index(
        &mut self,
        ix: usize,
        _window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) {
        self.selected = ix;
        self.preview(cx);
    }

    fn placeholder_text(&self, _window: &mut Window, _cx: &mut App) -> Arc<str> {
        "Select a theme...".into()
    }

    fn update_matches(
        &mut self,
        query: String,
        _window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) -> Task<()> {
        let kept = self.selected_theme().map(|meta| meta.name.clone());
        let query = query.to_lowercase();
        self.matches = (self.themes.iter().enumerate())
            .filter(|(_, meta)| meta.name.to_lowercase().contains(&query))
            .map(|(i, _)| i)
            .collect();
        self.selected = (self.matches.iter())
            .position(|&i| self.themes.get(i).map(|meta| &meta.name) == kept.as_ref())
            .unwrap_or_default();
        self.preview(cx);
        Task::ready(())
    }

    fn confirm(
        &mut self,
        _secondary: bool,
        _window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) {
        if let Some(meta) = self.selected_theme() {
            let system = SystemAppearance::global(cx).0;
            let chosen = choose_theme(&self.original.theme, &meta.name, meta.appearance, system);
            self.settled = true;
            save_settings(
                "theme",
                move |content| content.theme.theme = Some(chosen),
                cx,
            );
        }
        self.close(cx);
    }

    fn dismissed(&mut self, _window: &mut Window, cx: &mut Context<'_, Picker<Self>>) {
        self.revert(cx);
        self.close(cx);
    }

    fn render_match(
        &self,
        ix: usize,
        selected: bool,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> Option<Self::ListItem> {
        let meta = self.themes.get(*self.matches.get(ix)?)?;
        let appearance = match meta.appearance {
            Appearance::Dark => "dark",
            Appearance::Light => "light",
        };
        let shown = meta.name == self.original_name;
        let note = if shown { "shown" } else { appearance };
        Some(
            ListItem::new(ix)
                .inset(true)
                .spacing(ListItemSpacing::Sparse)
                .toggle_state(selected)
                .child(Label::new(meta.name.clone()))
                .end_slot(Label::new(note).color(Color::Muted)),
        )
    }
}
