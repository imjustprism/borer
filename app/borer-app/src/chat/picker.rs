//! The chat's model picker: the popover under the header's provider button, listing the
//! providers, the picked one's models and its key field.

use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, App, Context, DismissEvent, Entity, EventEmitter, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, WeakEntity, Window, div, px,
};
use ui::{
    ActiveTheme as _, ButtonCommon as _, ButtonStyle, Clickable as _, Color, Icon, IconButton,
    IconName, IconSize, Label, LabelCommon as _, LabelSize, ListItem, ListItemSpacing,
    ListSubHeader, StyledExt as _, TintColor, Tooltip, h_flex, v_flex,
};

use borer_engine::text;

use super::providers::{Endpoint, Offered};
use super::view::text_button;
use super::{ChatPanel, ForgetChatKey};

/// Width of the picker's popover.
const WIDTH: f32 = 320.0;

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

    /// Returns a section's heading, as Zed's menus head theirs.
    fn heading(text: &'static str) -> impl IntoElement {
        div().pt_1().child(ListSubHeader::new(text).inset(true))
    }

    /// Returns a row of the picker as Zed's model selector draws one: an icon, its name, what
    /// ends it, and a check when it is the one picked.
    fn row(
        id: SharedString,
        icon: IconName,
        name: String,
        end: Option<AnyElement>,
        picked: bool,
    ) -> ListItem {
        let color = if picked { Color::Accent } else { Color::Muted };
        ListItem::new(id)
            .inset(true)
            .spacing(ListItemSpacing::Sparse)
            .start_slot(Icon::new(icon).size(IconSize::Small).color(color))
            .child(Label::new(name).truncate())
            .end_slot(
                h_flex()
                    .min_w_0()
                    .gap_1p5()
                    .children(end)
                    .when(picked, |end| {
                        end.child(
                            Icon::new(IconName::Check)
                                .size(IconSize::Small)
                                .color(Color::Accent),
                        )
                    }),
            )
    }

    /// Returns the question the key row's forget button asks, with its two answers, once
    /// it was pressed; nothing is deleted before Forget.
    fn forget(&self) -> impl IntoElement {
        let (yes, no) = (self.panel.clone(), self.panel.clone());
        h_flex()
            .px_2()
            .pb_2()
            .gap_1()
            .child(
                div().flex_1().child(
                    Label::new("Forget the saved key? Only borer's own keychain entry is deleted.")
                        .size(LabelSize::Small)
                        .color(Color::Warning),
                ),
            )
            .child(
                text_button("chat-keep-key", "Keep", ButtonStyle::Outlined).on_click(
                    move |_, _, cx| {
                        no.update(cx, |panel, cx| {
                            panel.forgetting = false;
                            cx.notify();
                        })
                        .unwrap_or(());
                    },
                ),
            )
            .child(
                text_button(
                    "chat-forget-key",
                    "Forget",
                    ButtonStyle::Tinted(TintColor::Error),
                )
                .on_click(move |_, _, cx| {
                    yes.update(cx, |panel, cx| panel.forget_key(cx))
                        .unwrap_or(());
                }),
            )
    }

    /// Returns the key footer: the masked field, Save, and the button that asks to forget
    /// the saved key, with its question under it once pressed.
    fn key_row(
        &self,
        key: &Entity<editor::Editor>,
        forgetting: bool,
        cx: &App,
    ) -> impl IntoElement {
        let (weak, ask) = (self.panel.clone(), self.panel.clone());
        let colors = cx.theme().colors();
        v_flex()
            .mt_1()
            .border_t_1()
            .border_color(colors.border_variant)
            .child(
                h_flex()
                    .px_2()
                    .pt_2()
                    .pb_1()
                    .gap_1()
                    .child(
                        div()
                            .min_w_0()
                            .flex_1()
                            .h_7()
                            .flex()
                            .items_center()
                            .px_1p5()
                            .rounded_md()
                            .border_1()
                            .border_color(colors.border)
                            .bg(colors.editor_background)
                            .child(div().w_full().child(key.clone())),
                    )
                    .child(
                        text_button(
                            "chat-save-key",
                            "Save",
                            ButtonStyle::Tinted(TintColor::Accent),
                        )
                        .on_click(move |_, window, cx| {
                            weak.update(cx, |panel, cx| panel.save_key(window, cx))
                                .unwrap_or(());
                        }),
                    )
                    .child(
                        IconButton::new("chat-ask-forget", IconName::Trash)
                            .icon_size(IconSize::Small)
                            .icon_color(Color::Muted)
                            .tooltip(Tooltip::for_action_title(
                                "Forget Saved Key",
                                &ForgetChatKey,
                            ))
                            .on_click(move |_, window, cx| {
                                ask.update(cx, |panel, cx| panel.ask_to_forget(window, cx))
                                    .unwrap_or(());
                            }),
                    ),
            )
            .child(
                div().px_2().pb_2().child(
                    Label::new("The key is kept in the system keychain.")
                        .size(LabelSize::Small)
                        .color(Color::Muted),
                ),
            )
            .when(forgetting, |key| key.child(self.forget()))
    }

    /// Returns the row of `offer`: its icon and name, where it sends, and whether it is
    /// picked.
    fn provider(&self, offer: Offered, picked: bool, cx: &App) -> impl IntoElement {
        let panel = self.panel.clone();
        let hint = Label::new(Endpoint::of(offer, cx).host())
            .size(LabelSize::Small)
            .color(Color::Muted)
            .truncate();
        let id = SharedString::from(format!("chat-provider-{}", offer.label()));
        Self::row(
            id,
            offer.icon(),
            offer.label().to_owned(),
            Some(hint.into_any_element()),
            picked,
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
            Self::row(
                SharedString::from(format!("chat-model-{id}")),
                m.endpoint.offered.icon(),
                text::visible(&m.model.name.0).into_owned(),
                None,
                chosen.as_ref() == Some(&id),
            )
            .on_click(move |_, _, cx| {
                weak.update(cx, |panel, cx| panel.choose_model(&id, cx))
                    .unwrap_or(());
            })
        });
        let listing =
            (picked.is_some() && panel.models.is_empty() && panel.error.is_none()).then(|| {
                div().px_3().py_1().child(
                    Label::new("Asking for its models")
                        .size(LabelSize::Small)
                        .color(Color::Muted),
                )
            });
        let key = picked
            .filter(|offer| offer.key_var().is_some())
            .map(|_| self.key_row(&panel.key, panel.forgetting, cx));
        let error = panel.error.clone().map(|e| {
            div()
                .px_3()
                .pb_2()
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
            .child(v_flex().children(providers))
            .children(picked.map(|_| Self::heading("Model")))
            .child(
                v_flex()
                    .id("chat-picker-models")
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
