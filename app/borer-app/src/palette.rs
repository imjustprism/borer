//! Keyboard command palette state and overlay rendering over [`ACTION_REGISTRY`].

use gpui::{
    AnyElement, Context, FocusHandle, Hsla, InteractiveElement as _, IntoElement, KeyDownEvent,
    MouseButton, ParentElement as _, SharedString, StatefulInteractiveElement as _, Styled as _,
    Window, div, px,
};
use theme::ActiveTheme as _;

use crate::actions::{ACTION_REGISTRY, ActionId, ActionSpec};
use crate::app_view::AppView;

/// Pure state for the keyboard-openable command palette listing [`ACTION_REGISTRY`].
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct CommandPalette {
    /// Whether the palette overlay is currently visible.
    open: bool,
    /// Case-insensitive substring query entered by the user.
    query: String,
    /// Zero-based index of the highlighted row among [`Self::matches`].
    selected: usize,
}

impl CommandPalette {
    /// Creates a closed [`CommandPalette`] with an empty query.
    ///
    /// # Returns
    ///
    /// Initialized [`CommandPalette`].
    #[must_use]
    pub const fn new() -> Self {
        Self {
            open: false,
            query: String::new(),
            selected: 0,
        }
    }

    /// Reports whether the command palette is currently open.
    ///
    /// # Returns
    ///
    /// `true` while the overlay is visible.
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.open
    }

    /// Returns the active filter query text.
    ///
    /// # Returns
    ///
    /// Current query slice.
    #[must_use]
    pub fn query(&self) -> &str {
        &self.query
    }

    /// Returns the highlighted match index.
    ///
    /// # Returns
    ///
    /// Zero-based index within [`Self::matches`].
    #[must_use]
    pub const fn selected(&self) -> usize {
        self.selected
    }

    /// Opens the palette and resets the query and selection.
    pub fn open(&mut self) {
        self.open = true;
        self.query.clear();
        self.selected = 0;
    }

    /// Closes the palette and clears its query.
    pub fn close(&mut self) {
        self.open = false;
        self.query.clear();
        self.selected = 0;
    }

    /// Appends `text` to the query and resets selection to the top match.
    ///
    /// # Arguments
    ///
    /// * `text` - Non-control text typed by the user.
    pub fn push_query(&mut self, text: &str) {
        self.query.push_str(text);
        self.selected = 0;
    }

    /// Removes the last character from the query and clamps selection.
    pub fn backspace(&mut self) {
        let _ = self.query.pop();
        self.selected = 0;
    }

    /// Moves the highlighted match index by `delta`, clamping to valid bounds.
    ///
    /// # Arguments
    ///
    /// * `delta` - Signed row offset (`1` or `-1`).
    pub fn step_selection(&mut self, delta: isize) {
        let len = self.matches().len();
        if len == 0 {
            self.selected = 0;
            return;
        }
        self.selected = self
            .selected
            .saturating_add_signed(delta)
            .min(len.saturating_sub(1));
    }

    /// Returns every [`ActionSpec`] in [`ACTION_REGISTRY`] matching [`Self::query`].
    ///
    /// # Returns
    ///
    /// Matching action specifications in registration order.
    #[must_use]
    pub fn matches(&self) -> Vec<&'static ActionSpec> {
        let needle = self.query.trim().to_ascii_lowercase();
        if needle.is_empty() {
            return ACTION_REGISTRY.iter().collect();
        }
        ACTION_REGISTRY
            .iter()
            .filter(|spec| {
                spec.summary.to_ascii_lowercase().contains(&needle)
                    || spec.name.to_ascii_lowercase().contains(&needle)
                    || spec.shortcut.to_ascii_lowercase().contains(&needle)
            })
            .collect()
    }

    /// Resolves the currently highlighted [`ActionId`] and closes the palette.
    ///
    /// # Returns
    ///
    /// Selected [`ActionId`], or `None` when [`Self::matches`] is empty.
    #[must_use]
    pub fn confirm_selected(&mut self) -> Option<ActionId> {
        let chosen = self.matches().get(self.selected).map(|spec| spec.id);
        self.close();
        chosen
    }

    /// Selects match `ix` directly and closes the palette.
    ///
    /// # Arguments
    ///
    /// * `ix` - Match index clicked by the user.
    ///
    /// # Returns
    ///
    /// Chosen [`ActionId`], or `None` if `ix` is out of bounds.
    #[must_use]
    pub fn confirm_index(&mut self, ix: usize) -> Option<ActionId> {
        let chosen = self.matches().get(ix).map(|spec| spec.id);
        self.close();
        chosen
    }
}

/// Handles a [`KeyDownEvent`] while the command palette overlay has focus.
///
/// # Arguments
///
/// * `palette` - Mutable [`CommandPalette`] state.
/// * `root_focus` - Root [`FocusHandle`] restored before dispatching an action.
/// * `event` - GPUI [`KeyDownEvent`].
/// * `window` - Window dispatching the chosen action.
/// * `cx` - Owning [`AppView`] context.
pub fn handle_palette_key_down(
    palette: &mut CommandPalette,
    root_focus: &FocusHandle,
    event: &KeyDownEvent,
    window: &mut Window,
    cx: &mut Context<'_, AppView>,
) {
    let mods = event.keystroke.modifiers;
    if mods.control || mods.alt || mods.platform {
        return;
    }
    match event.keystroke.key.as_str() {
        "escape" => {
            palette.close();
            window.focus(root_focus, cx);
            cx.notify();
        }
        "down" => {
            palette.step_selection(1);
            cx.notify();
        }
        "up" => {
            palette.step_selection(-1);
            cx.notify();
        }
        "backspace" => {
            palette.backspace();
            cx.notify();
        }
        "enter" => {
            let chosen = palette.confirm_selected();
            window.focus(root_focus, cx);
            if let Some(id) = chosen
                && id != ActionId::TogglePalette
            {
                window.dispatch_action(id.boxed_action(), cx);
            }
            cx.notify();
        }
        _ => {
            if let Some(ch) = &event.keystroke.key_char
                && !ch.is_empty()
                && ch.chars().all(|c| !c.is_control())
            {
                palette.push_query(ch);
                cx.notify();
            }
        }
    }
}

/// Builds the clickable result rows displayed inside [`render_palette_overlay`].
///
/// # Arguments
///
/// * `palette` - Active [`CommandPalette`] state.
/// * `selected_bg` - Background color for the highlighted row.
/// * `text_muted` - Muted foreground color for keyboard shortcut hints.
/// * `cx` - Owning [`AppView`] context.
///
/// # Returns
///
/// Row elements for every matching action, or an empty-state placeholder row.
fn render_palette_rows(
    palette: &CommandPalette,
    selected_bg: Hsla,
    text_muted: Hsla,
    cx: &Context<'_, AppView>,
) -> Vec<AnyElement> {
    let items = palette.matches();
    if items.is_empty() {
        return vec![
            div()
                .px(px(10.0))
                .py(px(6.0))
                .text_color(text_muted)
                .child("No matching commands")
                .into_any_element(),
        ];
    }
    let selected_ix = palette.selected();
    let weak = cx.entity().downgrade();
    items
        .into_iter()
        .enumerate()
        .map(|(ix, spec)| {
            let entity = weak.clone();
            let row = div()
                .id(("palette-item", ix))
                .px(px(10.0))
                .py(px(5.0))
                .flex()
                .flex_row()
                .justify_between()
                .cursor_pointer()
                .on_click(move |_, window, cx| {
                    let _ = entity.update(cx, |view, cx| {
                        view.execute_palette_index(ix, window, cx);
                    });
                })
                .child(SharedString::from(spec.summary))
                .child(
                    div()
                        .text_color(text_muted)
                        .child(SharedString::from(spec.shortcut)),
                );
            if ix == selected_ix {
                row.bg(selected_bg).into_any_element()
            } else {
                row.into_any_element()
            }
        })
        .collect()
}

/// Renders the modal command palette overlay above [`AppView`].
///
/// # Arguments
///
/// * `palette` - Active [`CommandPalette`] state.
/// * `palette_focus` - [`FocusHandle`] bound to the palette query input.
/// * `cx` - Owning [`AppView`] context.
///
/// # Returns
///
/// Full-window modal overlay [`AnyElement`] that blocks background clicks and dismisses on outside click.
pub fn render_palette_overlay(
    palette: &CommandPalette,
    palette_focus: &FocusHandle,
    cx: &mut Context<'_, AppView>,
) -> AnyElement {
    let (surface_bg, bg, border_col, border_focused, selected_bg, text_muted) = {
        let colors = cx.theme().colors();
        (
            colors.elevated_surface_background,
            colors.background,
            colors.border,
            colors.border_focused,
            colors.element_selected,
            colors.text_muted,
        )
    };
    let query_display = if palette.query().is_empty() {
        SharedString::from("Type a command or shortcut... |")
    } else {
        SharedString::from(format!("{}|", palette.query()))
    };
    let rows = render_palette_rows(palette, selected_bg, text_muted, cx);

    div()
        .id("palette-backdrop")
        .occlude()
        .absolute()
        .inset_0()
        .pt(px(36.0))
        .flex()
        .items_start()
        .justify_center()
        .on_mouse_down(
            MouseButton::Left,
            cx.listener(|view, _, window, cx| {
                view.dismiss_palette(window, cx);
                cx.stop_propagation();
            }),
        )
        .on_mouse_down(
            MouseButton::Right,
            cx.listener(|view, _, window, cx| {
                view.dismiss_palette(window, cx);
                cx.stop_propagation();
            }),
        )
        .child(
            div()
                .id("command-palette")
                .track_focus(palette_focus)
                .on_key_down(cx.listener(AppView::on_palette_key_down))
                .on_mouse_down(MouseButton::Left, |_, _, cx| cx.stop_propagation())
                .on_mouse_down(MouseButton::Right, |_, _, cx| cx.stop_propagation())
                .w(px(520.0))
                .bg(surface_bg)
                .border_1()
                .border_color(border_focused)
                .flex()
                .flex_col()
                .child(
                    div()
                        .px(px(10.0))
                        .py(px(6.0))
                        .bg(bg)
                        .border_b_1()
                        .border_color(border_col)
                        .child(query_display),
                )
                .children(rows),
        )
        .into_any_element()
}

#[cfg(test)]
mod tests {
    use crate::actions::{ACTION_REGISTRY, ActionId};

    use super::CommandPalette;

    /// Filtering, stepping, and confirming in [`CommandPalette`] resolve registered [`ActionId`]s.
    ///
    /// # Panics
    ///
    /// Panics if [`CommandPalette`] misses a registered action or selects the wrong item.
    #[test]
    fn command_palette_filters_and_confirms_registered_actions() {
        let mut palette = CommandPalette::new();
        assert!(!palette.is_open());
        palette.open();
        assert!(palette.is_open());
        assert_eq!(palette.matches().len(), ACTION_REGISTRY.len());

        palette.push_query("measure");
        let filtered = palette.matches();
        assert_eq!(filtered.len(), 1);
        assert_eq!(filtered[0].id, ActionId::Measure);
        assert_eq!(palette.confirm_selected(), Some(ActionId::Measure));
        assert!(!palette.is_open());

        palette.open();
        palette.push_query("navigate");
        assert_eq!(palette.matches().len(), 2);
        palette.step_selection(1);
        assert_eq!(palette.confirm_selected(), Some(ActionId::GoForward));
    }
}
