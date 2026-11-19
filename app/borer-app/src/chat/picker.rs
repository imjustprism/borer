//! The chat's model picker: the popover under the header's provider button, listing the
//! providers, the picked one's models and its key field.

use gpui::{
    App, Context, DismissEvent, Entity, EventEmitter, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, WeakEntity, Window, div, px,
};
use ui::{
    ActiveTheme as _, Button, Clickable as _, Color, Label, LabelCommon as _, LabelSize, ListItem,
    ListItemSpacing, StyledExt as _, Toggleable as _, h_flex, v_flex,
};

use borer_engine::text;

use super::ChatPanel;
use super::providers::{Endpoint, Offered};

/// Width of the picker's popover.
const WIDTH: f32 = 300.0;

/// The model picker's popover over the chat panel's state.
pub struct ChatPicker {
    /// The panel whose provider, models and key field the popover shows.
    panel: WeakEntity<ChatPanel>,
    /// Focus handle of the popover, which takes focus when it opens.
    focus_handle: FocusHandle,
    /// Redraws on the panel's changes: the models listed, a key saved, an error.
    _panel: Subscription,
}

impl ChatPicker {
    /// Returns the popover over `panel`.
    ///
    /// # Arguments
    ///
    /// * `panel` - The chat panel.
    /// * `cx` - Popover context.
    #[must_use]
    pub fn new(panel: &Entity<ChatPanel>, cx: &mut Context<'_, Self>) -> Self {
        Self {
            panel: panel.downgrade(),
            focus_handle: cx.focus_handle(),
            _panel: cx.observe(panel, |_, _, cx| cx.notify()),
        }
    }

    /// Returns a section's heading.
    fn heading(text: &'static str) -> impl IntoElement {
        div()
            .px_2()
            .pt_1p5()
            .pb_0p5()
            .child(Label::new(text).size(LabelSize::XSmall).color(Color::Muted))
    }

    /// Returns the way to forget the saved key: a quiet button, then once pressed the
    /// question and its two answers; nothing is deleted before Forget.
    fn forget(&self, asking: bool) -> impl IntoElement {
        let (yes, no, ask) = (self.panel.clone(), self.panel.clone(), self.panel.clone());
        let row = h_flex().px_2().pb_1().gap_1();
        if asking {
            return row
                .child(
                    div().flex_1().child(
                        Label::new(
                            "Forget the saved key? Only borer's own keychain entry is deleted.",
                        )
                        .size(LabelSize::Small)
                        .color(Color::Warning),
                    ),
                )
                .child(
                    Button::new("chat-keep-key", "Keep").on_click(move |_, _, cx| {
                        no.update(cx, |panel, cx| {
                            panel.forgetting = false;
                            cx.notify();
                        })
                        .unwrap_or(());
                    }),
                )
                .child(
                    Button::new("chat-forget-key", "Forget").on_click(move |_, _, cx| {
                        yes.update(cx, |panel, cx| panel.forget_key(cx))
                            .unwrap_or(());
                    }),
                );
        }
        row.child(div().flex_1()).child(
            Button::new("chat-ask-forget", "Forget saved key")
                .label_size(LabelSize::XSmall)
                .color(Color::Muted)
                .on_click(move |_, window, cx| {
                    ask.update(cx, |panel, cx| panel.ask_to_forget(window, cx))
                        .unwrap_or(());
                }),
        )
    }

    /// Returns the row of `offer`: its name, whether it is picked, and where it sends.
    fn provider(&self, offer: Offered, picked: bool, cx: &App) -> impl IntoElement {
        let panel = self.panel.clone();
        let hint = Endpoint::of(offer, cx).host();
        ListItem::new(SharedString::from(format!(
            "chat-provider-{}",
            offer.label()
        )))
        .spacing(ListItemSpacing::Sparse)
        .toggle_state(picked)
        .child(Label::new(offer.label()).size(LabelSize::Small))
        .end_slot(
            Label::new(hint)
                .size(LabelSize::XSmall)
                .color(Color::Muted)
                .truncate(),
        )
        .on_click(move |_, window, cx| {
            panel
                .update(cx, |panel, cx| panel.switch(offer, window, cx))
                .unwrap_or(());
        })
    }
}

impl std::fmt::Debug for ChatPicker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ChatPicker").finish_non_exhaustive()
    }
}

impl EventEmitter<DismissEvent> for ChatPicker {}

impl Focusable for ChatPicker {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Render for ChatPicker {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let Some(panel) = self.panel.upgrade() else {
            return div().into_any_element();
        };
        let panel = panel.read(cx);
        let picked = panel.picked;
        let chosen = panel.thread.read(cx).chosen().map(|c| c.model.id.0.clone());
        let providers = Offered::ALL.map(|offer| self.provider(offer, picked == Some(offer), cx));
        let weak = self.panel.clone();
        let models = panel.models.iter().map(|m| {
            let id = m.model.id.0.clone();
            let weak = weak.clone();
            ListItem::new(SharedString::from(format!("chat-model-{id}")))
                .spacing(ListItemSpacing::Sparse)
                .toggle_state(chosen.as_ref() == Some(&id))
                .child(
                    Label::new(text::visible(&m.model.name.0).into_owned())
                        .size(LabelSize::Small)
                        .truncate(),
                )
                .on_click(move |_, _, cx| {
                    weak.update(cx, |panel, cx| panel.choose_model(&id, cx))
                        .unwrap_or(());
                })
        });
        let listing =
            (picked.is_some() && panel.models.is_empty() && panel.error.is_none()).then(|| {
                div().px_2().py_1().child(
                    Label::new("Asking for its models")
                        .size(LabelSize::Small)
                        .color(Color::Muted),
                )
            });
        let key = picked.filter(|offer| offer.key_var().is_some()).map(|_| {
            let weak = self.panel.clone();
            v_flex()
                .child(Self::heading("API key, kept in the system keychain"))
                .child(
                    h_flex()
                        .px_2()
                        .pb_1()
                        .gap_1()
                        .child(
                            div()
                                .flex_1()
                                .px_1()
                                .py_0p5()
                                .rounded_sm()
                                .border_1()
                                .border_color(cx.theme().colors().border)
                                .bg(cx.theme().colors().editor_background)
                                .child(panel.key.clone()),
                        )
                        .child(Button::new("chat-save-key", "Save").on_click(
                            move |_, window, cx| {
                                weak.update(cx, |panel, cx| panel.save_key(window, cx))
                                    .unwrap_or(());
                            },
                        )),
                )
                .child(self.forget(panel.forgetting))
        });
        let error = panel.error.clone().map(|e| {
            div()
                .px_2()
                .pb_1()
                .child(Label::new(e).size(LabelSize::Small).color(Color::Error))
        });
        v_flex()
            .id("chat-picker")
            .key_context("ChatPicker")
            .track_focus(&self.focus_handle)
            .w(px(WIDTH))
            .elevation_2(cx)
            .py_1()
            .on_action(cx.listener(|_, _: &menu::Cancel, _, cx| cx.emit(DismissEvent)))
            .on_action(cx.listener(|this, _: &menu::Confirm, window, cx| {
                this.panel
                    .update(cx, |panel, cx| panel.save_key(window, cx))
                    .unwrap_or(());
            }))
            .on_mouse_down_out(cx.listener(|_, _, _, cx| cx.emit(DismissEvent)))
            .child(Self::heading("Provider"))
            .child(v_flex().px_1().children(providers))
            .children(picked.map(|_| Self::heading("Model")))
            .child(
                v_flex()
                    .id("chat-picker-models")
                    .px_1()
                    .max_h(px(180.0))
                    .overflow_y_scroll()
                    .children(models),
            )
            .children(listing)
            .children(key)
            .children(error)
            .into_any_element()
    }
}
