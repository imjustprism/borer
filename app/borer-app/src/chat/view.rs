//! How the chat panel draws: its header, the thread's entries as a document, the bars above
//! the input, the input, and the empty state.
//!
//! A model's reply is drawn from its text written out ([`text::visible`]): fenced code and
//! code spans in the editor's font, everything else as plain text, so nothing in it hides,
//! links or loads from anywhere.

use std::ops::Range;

use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, AppContext as _, Context, HighlightStyle, InteractiveElement as _, IntoElement,
    ParentElement as _, SharedString, StatefulInteractiveElement as _, Styled as _, StyledText,
    div, px,
};
use theme_settings::ThemeSettings;
use ui::{
    ActiveTheme as _, Banner, Button, ButtonCommon as _, ButtonStyle, Clickable as _, Color,
    CommonAnimationExt as _, CopyButton, Disableable as _, Disclosure, Icon, IconButton, IconName,
    IconSize, Indicator, Label, LabelCommon as _, LabelSize, PopoverMenu, Severity,
    StyledTypography as _, Tooltip, h_flex, v_flex,
};

use borer_engine::text;
use settings::Settings as _;

use super::picker::ChatPicker;
use super::thread::{Arg, Call, Chosen, Entry, Fault, Ran};
use super::{ChatPanel, NewChatThread, StopChat};

/// Three questions a reverse engineer asks first of an open binary.
pub(crate) const EXAMPLES: [&str; 3] = [
    "What does this binary do, and which functions should I read first?",
    "How does it read its command line and settings?",
    "Is anything packed, encrypted or checking for a debugger?",
];

/// Height of the header row and of a tool call's row.
const ROW: f32 = 28.0;

/// One block of a reply: running text, or a fenced code block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Block<'a> {
    /// Running text, which may hold code spans.
    Text(&'a str),
    /// The lines of a fenced code block, without its fences.
    Code(Vec<&'a str>),
}

/// Returns `text` split into running text and fenced code blocks; an unclosed fence runs to
/// the end, as a reply still streaming has it.
#[must_use]
pub(crate) fn blocks(text: &str) -> Vec<Block<'_>> {
    let mut blocks = Vec::new();
    let (mut code, mut start, mut at) = (None::<Vec<&str>>, 0, 0);
    for line in text.split_inclusive('\n') {
        let fence = line.trim_start().starts_with("```");
        match (&mut code, fence) {
            (None, true) => {
                let before = text.get(start..at).unwrap_or_default().trim_matches('\n');
                if !before.trim().is_empty() {
                    blocks.push(Block::Text(before));
                }
                code = Some(Vec::new());
            }
            (Some(lines), true) => {
                blocks.push(Block::Code(std::mem::take(lines)));
                code = None;
                start = at.saturating_add(line.len());
            }
            (Some(lines), false) => lines.push(line.trim_end_matches(['\n', '\r'])),
            (None, false) => {}
        }
        at = at.saturating_add(line.len());
        if code.is_none() && fence {
            start = at;
        }
    }
    match code {
        Some(lines) => blocks.push(Block::Code(lines)),
        None => {
            let rest = text.get(start..).unwrap_or_default().trim_matches('\n');
            if !rest.trim().is_empty() {
                blocks.push(Block::Text(rest));
            }
        }
    }
    blocks
}

/// Returns `text` with its code spans' backticks dropped, and the byte ranges of the spans
/// in what is returned; a backtick with no partner is kept as written.
#[must_use]
pub(crate) fn spans(text: &str) -> (String, Vec<Range<usize>>) {
    let (mut out, mut ranges) = (String::with_capacity(text.len()), Vec::new());
    let mut rest = text;
    while let Some(open) = rest.find('`') {
        let after = rest.get(open.saturating_add(1)..).unwrap_or_default();
        let Some(close) = after.find('`').filter(|&c| c > 0) else {
            break;
        };
        out.push_str(rest.get(..open).unwrap_or_default());
        let start = out.len();
        out.push_str(after.get(..close).unwrap_or_default());
        ranges.push(start..out.len());
        rest = after.get(close.saturating_add(1)..).unwrap_or_default();
    }
    out.push_str(rest);
    (out, ranges)
}

/// Returns a byte count as a person reads it: `812 B`, `4.1 KB`.
fn size_of(bytes: usize) -> String {
    if bytes < 1024 {
        return format!("{bytes} B");
    }
    let tenths = bytes.saturating_mul(10) / 1024;
    format!("{}.{} KB", tenths / 10, tenths % 10)
}

/// Returns where the header says `chosen`'s requests go.
///
/// It is `local` only when nothing sent to it leaves the machine ([`Chosen::is_local`],
/// the one rule the notice and the turn's binding also ask), else `sends to` and its
/// endpoint's host.
pub(crate) fn hint(chosen: &Chosen) -> String {
    if chosen.is_local() {
        "local".to_owned()
    } else {
        format!("sends to {}", chosen.endpoint.host())
    }
}

/// Returns the icon of the tool `name` by its catalog row: one that only reads, one that
/// proposes edits, or one the catalog does not have.
fn icon_of(name: &str) -> IconName {
    match borer_front::tools::tool(name).map(|t| t.hints.read_only) {
        Some(true) => IconName::FileCode,
        Some(false) => IconName::Pencil,
        None => IconName::ToolHammer,
    }
}

impl ChatPanel {
    /// Returns the header: the picker's button with where it sends, the thread's state as
    /// a dot, and New Thread.
    pub(super) fn header(&self, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let thread = self.thread.read(cx);
        let chosen = thread.chosen();
        let label = chosen.map_or_else(
            || "Pick a model".to_owned(),
            |c| {
                let name = text::visible(&c.model.name.0);
                format!("{} \u{b7} {name}", c.endpoint.offered.label())
            },
        );
        let hint = chosen.map(hint);
        let waits = thread.held().is_some() || thread.head().is_some();
        let (dot, said) = match (thread.is_running(), waits, chosen) {
            (true, _, _) => (Color::Accent, "Running: the model is answering"),
            (false, true, _) => (Color::Warning, "Waiting on you"),
            (false, false, Some(_)) => (Color::Muted, "Idle"),
            (false, false, None) => (Color::Disabled, "No model picked"),
        };
        let panel = cx.entity();
        let picker = PopoverMenu::new("chat-picker")
            .menu(move |_, cx| Some(cx.new(|cx| ChatPicker::new(&panel, cx))))
            .trigger(
                Button::new("chat-pick", label)
                    .style(ButtonStyle::Subtle)
                    .label_size(LabelSize::Small)
                    .truncate(true)
                    .end_icon(Icon::new(IconName::ChevronDown).size(IconSize::XSmall)),
            )
            .with_handle(self.picker.clone())
            .anchor(gpui::Anchor::TopLeft)
            .offset(gpui::point(px(0.0), px(2.0)));
        h_flex()
            .h(px(ROW + 4.0))
            .flex_none()
            .pl_1()
            .pr_2()
            .gap_1()
            .border_b_1()
            .border_color(cx.theme().colors().border_variant)
            .child(div().min_w_0().child(picker))
            .children(hint.map(|hint| {
                div().min_w_0().flex_1().child(
                    Label::new(hint)
                        .size(LabelSize::XSmall)
                        .color(Color::Muted)
                        .truncate(),
                )
            }))
            .when(chosen.is_none(), |row| row.child(div().flex_1()))
            .child(
                div()
                    .id("chat-status")
                    .px_1()
                    .tooltip(Tooltip::text(said))
                    .child(Indicator::dot().color(dot)),
            )
            .child(
                IconButton::new("chat-new-thread", IconName::Plus)
                    .icon_size(IconSize::Small)
                    .tooltip(Tooltip::for_action_title("New Thread", &NewChatThread))
                    .on_click(cx.listener(|this, _, _, cx| {
                        this.thread.update(cx, super::thread::Thread::clear);
                    })),
            )
    }

    /// Returns entry `ix` of the thread as the person sees it.
    pub(super) fn entry(&self, ix: usize, cx: &mut Context<'_, Self>) -> AnyElement {
        let thread = self.thread.read(cx);
        let Some(entry) = thread.entries().get(ix) else {
            return div().into_any_element();
        };
        let turn_start = ix > 0 && matches!(entry, Entry::Person(_));
        let body = match entry {
            Entry::Person(said) => person(&text::visible(said), cx),
            Entry::Model(said) => {
                let first = !thread
                    .entries()
                    .get(..ix)
                    .unwrap_or_default()
                    .iter()
                    .rev()
                    .take_while(|e| !matches!(e, Entry::Person(_)))
                    .any(|e| matches!(e, Entry::Model(_)));
                let name = first
                    .then(|| {
                        let chosen = thread.chosen()?;
                        Some(SharedString::from(
                            text::visible(&chosen.model.name.0).into_owned(),
                        ))
                    })
                    .flatten();
                model(ix, said, name, cx)
            }
            Entry::Tool(_) => match thread.call_at(ix).cloned() {
                Some(call) => self.tool(&call, cx),
                None => div().into_any_element(),
            },
            Entry::Notice(said) => {
                let held = thread
                    .held_notice()
                    .is_some_and(|n| std::ptr::eq(n, said.as_str()));
                if held {
                    div().into_any_element()
                } else {
                    quiet(IconName::Info, &text::visible(said))
                }
            }
            Entry::Error(said) => {
                let said = text::visible(said).into_owned();
                self.error(ix, &said, cx)
            }
            Entry::Proposal(id) => self.card(*id, cx),
        };
        div()
            .when(turn_start, |d| {
                d.mt_4()
                    .pt_4()
                    .border_t_1()
                    .border_color(cx.theme().colors().border_variant)
            })
            .when(ix == 0, |d| d.pt_2())
            .child(body)
            .into_any_element()
    }

    /// Returns the row of a tool call: its tool, what it reads, its state, and once opened
    /// its arguments and the first lines of its answer.
    fn tool(&self, call: &Call, cx: &mut Context<'_, Self>) -> AnyElement {
        let ix = call.entry;
        let open = self.opened.contains(&ix);
        let address = call
            .key
            .as_ref()
            .filter(|k| k.1 == Arg::Address)
            .and_then(|k| k.0.strip_prefix("0x"))
            .and_then(|hex| u64::from_str_radix(hex, 16).ok());
        let key = call.key.as_ref().map(|key| {
            let label = Label::new(text::visible(&key.0).into_owned())
                .size(LabelSize::Small)
                .buffer_font(cx)
                .truncate();
            match address {
                Some(va) => div()
                    .id(("chat-call-at", ix))
                    .min_w_0()
                    .cursor_pointer()
                    .hover(|s| s.underline())
                    .tooltip(Tooltip::text("Open this function"))
                    .on_click(cx.listener(move |this, _, window, cx| {
                        this.open_address(va, window, cx);
                    }))
                    .child(label.color(Color::Accent))
                    .into_any_element(),
                None => div()
                    .min_w_0()
                    .child(label.color(Color::Muted))
                    .into_any_element(),
            }
        });
        let state = match &call.ran {
            Ran::Running => Icon::new(IconName::LoadCircle)
                .size(IconSize::XSmall)
                .color(Color::Muted)
                .with_keyed_rotate_animation(("chat-call-spin", ix), 2)
                .into_any_element(),
            Ran::Answered { bytes, .. } => small(size_of(*bytes), Color::Muted),
            Ran::Failed(_) => small("refused".to_owned(), Color::Error),
            Ran::TimedOut => small("timed out".to_owned(), Color::Error),
            Ran::Cancelled => small("cancelled".to_owned(), Color::Muted),
        };
        let row = h_flex()
            .id(("chat-call", ix))
            .h(px(ROW))
            .px_2()
            .gap_1p5()
            .cursor_pointer()
            .hover(|s| s.bg(cx.theme().colors().ghost_element_hover))
            .on_click(cx.listener(move |this, _, _, cx| this.toggle_call(ix, cx)))
            .child(
                Disclosure::new(("chat-call-open", ix), open)
                    .on_click(cx.listener(move |this, _, _, cx| this.toggle_call(ix, cx))),
            )
            .child(
                Icon::new(icon_of(&call.name))
                    .size(IconSize::XSmall)
                    .color(Color::Muted),
            )
            .child(Label::new(text::visible(&call.name).into_owned()).size(LabelSize::Small))
            .children(key)
            .child(div().flex_1())
            .child(state);
        v_flex()
            .child(row)
            .when(open, |col| col.child(details(call, cx)))
            .into_any_element()
    }

    /// Returns an error the thread shows: quietly when it is a receipt, else as a callout
    /// with the one action that helps.
    fn error(&self, ix: usize, said: &str, cx: &mut Context<'_, Self>) -> AnyElement {
        let thread = self.thread.read(cx);
        let fix = |label: &'static str| Button::new(("chat-fix", ix), label);
        let action = match thread.fault_at(ix) {
            Some(Fault::Stopped) => return quiet(IconName::Stop, said),
            None | Some(Fault::NoBinary | Fault::Model) => None,
            Some(Fault::NoModel) => Some(
                fix("Pick a model")
                    .on_click(cx.listener(|this, _, window, cx| this.picker.show(window, cx))),
            ),
            Some(Fault::Spent) => {
                Some(fix("New Thread").on_click(cx.listener(|this, _, _, cx| {
                    this.thread.update(cx, super::thread::Thread::clear);
                })))
            }
            Some(Fault::Provider) => thread.retry_at(ix).map(|_| {
                fix("Retry").on_click(cx.listener(move |this, _, _, cx| this.retry(ix, cx)))
            }),
        };
        let action = action.map(|b| b.style(ButtonStyle::Subtle).label_size(LabelSize::Small));
        div()
            .px_2()
            .pt_2()
            .pb_1()
            .child(
                Banner::new()
                    .severity(Severity::Error)
                    .wrap_content(true)
                    .child(Label::new(said.to_owned()).size(LabelSize::Small))
                    .when_some(action, |b, a| b.action_slot(a)),
            )
            .into_any_element()
    }

    /// Returns the bars above the input: the turn that runs, the proposal that waits, and
    /// the agreement a held message waits on, with its two buttons beside what it explains.
    pub(super) fn bars(&self, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let thread = self.thread.read(cx);
        let working = thread.is_running().then(|| {
            let who = thread
                .chosen()
                .map_or_else(|| "The model".into(), |c| text::visible(&c.model.name.0));
            working(&who)
        });
        let waiting = thread
            .proposals()
            .iter()
            .filter(|p| matches!(p.verdict, super::thread::Verdict::Waiting))
            .count();
        let waits = thread.head().map(|_| {
            let said = match waiting {
                0 => "1 proposal needs you".to_owned(),
                1 => "1 proposal waits".to_owned(),
                n => format!("{n} proposals wait"),
            };
            h_flex()
                .id("chat-waits")
                .h(px(ROW))
                .px_2()
                .gap_1p5()
                .border_t_1()
                .border_color(cx.theme().colors().border_variant)
                .bg(cx.theme().colors().element_background)
                .cursor_pointer()
                .on_click(cx.listener(|this, _, window, cx| this.show_head(window, cx)))
                .child(
                    Icon::new(IconName::Pencil)
                        .size(IconSize::XSmall)
                        .color(Color::Warning),
                )
                .child(Label::new(said).size(LabelSize::Small))
                .child(div().flex_1())
                .child(
                    Label::new("Show")
                        .size(LabelSize::Small)
                        .color(Color::Accent),
                )
        });
        let notice = thread.held_notice().map(|said| {
            let said = text::visible(said).into_owned();
            div().px_2().pt_2().child(
                Banner::new()
                    .severity(Severity::Warning)
                    .wrap_content(true)
                    .child(Label::new(said).size(LabelSize::Small))
                    .action_slot(
                        h_flex()
                            .gap_1()
                            .child(
                                Button::new("chat-dont-send", "Don't Send")
                                    .style(ButtonStyle::Subtle)
                                    .label_size(LabelSize::Small)
                                    .on_click(cx.listener(|this, _, _, cx| {
                                        this.thread.update(cx, super::thread::Thread::decline);
                                    })),
                            )
                            .child(
                                Button::new("chat-send-held", "Send")
                                    .style(ButtonStyle::Filled)
                                    .label_size(LabelSize::Small)
                                    .on_click(cx.listener(|this, _, _, cx| {
                                        this.thread.update(cx, super::thread::Thread::agree);
                                    })),
                            ),
                    ),
            )
        });
        let error = self.error.clone().map(|e| {
            div().px_2().pt_2().child(
                Banner::new()
                    .severity(Severity::Error)
                    .wrap_content(true)
                    .child(Label::new(e).size(LabelSize::Small))
                    .action_slot(
                        Button::new("chat-error-pick", "Pick a model")
                            .style(ButtonStyle::Subtle)
                            .label_size(LabelSize::Small)
                            .on_click(cx.listener(|this, _, window, cx| {
                                this.picker.show(window, cx);
                            })),
                    ),
            )
        });
        v_flex()
            .flex_none()
            .children(working)
            .children(self.note.clone().map(|note| {
                div()
                    .px_2()
                    .pt_1()
                    .child(small(note.to_string(), Color::Muted))
            }))
            .children(waits)
            .children(notice)
            .children(error)
    }

    /// Returns the input: the editor, Send or Stop beside it, and a line with its keys or
    /// why it cannot send.
    pub(super) fn composer(&self, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let thread = self.thread.read(cx);
        let running = thread.is_running();
        let reason = thread.chosen().is_none().then_some("Pick a model to start");
        let colors = cx.theme().colors();
        let button = if running {
            IconButton::new("chat-stop", IconName::Stop)
                .icon_size(IconSize::Small)
                .icon_color(Color::Error)
                .tooltip(Tooltip::for_action_title("Stop", &StopChat))
                .on_click(cx.listener(|this, _, _, cx| {
                    this.thread.update(cx, super::thread::Thread::stop);
                }))
        } else {
            IconButton::new("chat-send", IconName::Send)
                .icon_size(IconSize::Small)
                .disabled(reason.is_some())
                .tooltip(Tooltip::text("Send"))
                .on_click(cx.listener(|this, _, window, cx| this.send(window, cx)))
        };
        let hint = match (reason, running) {
            (Some(reason), _) => small(reason.to_owned(), Color::Warning),
            (None, _) => small(
                "Enter sends \u{b7} Shift+Enter breaks a line".to_owned(),
                Color::Muted,
            ),
        };
        v_flex()
            .flex_none()
            .p_2()
            .gap_1()
            .child(
                h_flex()
                    .items_end()
                    .gap_1()
                    .pl_2()
                    .pr_1()
                    .py_1()
                    .rounded_md()
                    .border_1()
                    .border_color(colors.border)
                    .bg(colors.editor_background)
                    .child(div().flex_1().min_w_0().py_0p5().child(self.input.clone()))
                    .child(button),
            )
            .child(div().px_1().child(hint))
    }

    /// Returns what an empty thread shows: what the chat does, and three questions to ask,
    /// each sent by a click.
    pub(super) fn empty_state(&self, file: &str, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let can = self.thread.read(cx).chosen().is_some();
        let colors = cx.theme().colors();
        let chips = EXAMPLES.iter().enumerate().map(|(n, ask)| {
            div()
                .id(("chat-example", n))
                .px_2()
                .py_1()
                .rounded_sm()
                .border_1()
                .border_color(colors.border)
                .when(can, |chip| {
                    chip.cursor_pointer()
                        .hover(|s| s.bg(colors.ghost_element_hover))
                        .on_click(cx.listener(move |this, _, _, cx| {
                            this.thread
                                .update(cx, |t, cx| t.send((*ask).to_owned(), cx));
                        }))
                })
                .child(Label::new(*ask).size(LabelSize::Small).color(if can {
                    Color::Default
                } else {
                    Color::Disabled
                }))
        });
        v_flex()
            .flex_1()
            .justify_center()
            .px_4()
            .gap_3()
            .child(
                v_flex()
                    .gap_1()
                    .child(Label::new(format!("Ask about {file}")))
                    .child(
                        Label::new(
                            "The model reads the binary through borer's tools. Edits it proposes wait for you.",
                        )
                        .size(LabelSize::Small)
                        .color(Color::Muted),
                    ),
            )
            .child(v_flex().gap_1().children(chips))
    }
}

/// Returns the line that says `who` is answering, with a spinner.
fn working(who: &str) -> AnyElement {
    h_flex()
        .h(px(ROW))
        .px_2()
        .gap_1p5()
        .child(
            Icon::new(IconName::LoadCircle)
                .size(IconSize::XSmall)
                .color(Color::Muted)
                .with_rotate_animation(2),
        )
        .child(small(format!("{who} is answering"), Color::Muted))
        .into_any_element()
}

/// Returns a small label in `color`.
fn small(text: String, color: Color) -> AnyElement {
    Label::new(text)
        .size(LabelSize::XSmall)
        .color(color)
        .into_any_element()
}

/// Returns a quiet line of the thread: an icon and muted text.
fn quiet(icon: IconName, said: &str) -> AnyElement {
    h_flex()
        .px_2()
        .py_0p5()
        .gap_1p5()
        .items_start()
        .child(
            div()
                .pt(px(3.0))
                .child(Icon::new(icon).size(IconSize::XSmall).color(Color::Muted)),
        )
        .child(
            div().min_w_0().flex_1().child(
                Label::new(said.to_owned())
                    .size(LabelSize::Small)
                    .color(Color::Muted),
            ),
        )
        .into_any_element()
}

/// Returns a role's label over its text: `You`, or the model's name.
fn role(name: impl Into<SharedString>) -> impl IntoElement {
    Label::new(name)
        .size(LabelSize::XSmall)
        .weight(gpui::FontWeight::SEMIBOLD)
        .color(Color::Muted)
}

/// Returns what the person wrote.
fn person(said: &str, cx: &Context<'_, ChatPanel>) -> AnyElement {
    v_flex()
        .px_2()
        .pb_2()
        .gap_1()
        .child(role("You"))
        .child(prose(said, cx))
        .into_any_element()
}

/// Returns what the model wrote, written out ([`text::visible`]) under its name when it
/// opens the turn, with a copy button that shows on hover and copies the text as the model
/// wrote it.
fn model(
    ix: usize,
    said: &str,
    name: Option<SharedString>,
    cx: &Context<'_, ChatPanel>,
) -> AnyElement {
    let group = SharedString::from(format!("chat-model-{ix}"));
    v_flex()
        .group(group.clone())
        .px_2()
        .when(name.is_some(), |col| col.pt_4())
        .when(name.is_none(), |col| col.pt_1())
        .gap_1()
        .child(
            h_flex()
                .h(px(16.0))
                .children(name.map(role))
                .child(div().flex_1())
                .child(
                    CopyButton::new(("chat-copy", ix), said.to_owned())
                        .icon_size(IconSize::XSmall)
                        .tooltip_label("Copy reply")
                        .visible_on_hover(group),
                ),
        )
        .child(prose(&text::visible(said), cx))
        .into_any_element()
}

/// Returns `said` as running text and code blocks, code in the editor's font.
fn prose(said: &str, cx: &Context<'_, ChatPanel>) -> AnyElement {
    let settings = ThemeSettings::get_global(cx);
    let mono = settings.buffer_font.family.clone();
    let colors = cx.theme().colors();
    let span_bg = colors.element_background;
    v_flex()
        .gap_1p5()
        .text_ui_sm(cx)
        .line_height(gpui::relative(1.5))
        .text_color(colors.text)
        .children(blocks(said).into_iter().map(|block| {
            match block {
                Block::Text(text) => {
                    let (text, ranges) = spans(text);
                    let highlight = HighlightStyle {
                        background_color: Some(span_bg),
                        ..HighlightStyle::default()
                    };
                    let fonts = ranges
                        .iter()
                        .map(|r| (r.clone(), mono.clone()))
                        .collect::<Vec<_>>();
                    div()
                        .min_w_0()
                        .child(
                            StyledText::new(text)
                                .with_highlights(ranges.into_iter().map(|r| (r, highlight)))
                                .with_font_family_overrides(fonts),
                        )
                        .into_any_element()
                }
                Block::Code(lines) => v_flex()
                    .id(SharedString::from(format!(
                        "chat-code-{:p}",
                        lines.as_ptr()
                    )))
                    .p_2()
                    .rounded_sm()
                    .border_1()
                    .border_color(colors.border_variant)
                    .bg(colors.editor_background)
                    .overflow_x_scroll()
                    .children(lines.into_iter().map(|line| {
                        Label::new(line.to_owned())
                            .size(LabelSize::Small)
                            .buffer_font(cx)
                            .single_line()
                    }))
                    .into_any_element(),
            }
        }))
        .into_any_element()
}

/// Returns an opened tool call's arguments and the first lines of its answer, the answer
/// in the editor's font: it is data from the binary.
fn details(call: &Call, cx: &Context<'_, ChatPanel>) -> impl IntoElement {
    let mono = |text: &str, color: Color| {
        Label::new(text::visible(text).into_owned())
            .size(LabelSize::XSmall)
            .buffer_font(cx)
            .color(color)
            .single_line()
    };
    let lines = |text: &str, color: Color| {
        v_flex()
            .children(text.lines().map(|line| mono(line, color)))
            .into_any_element()
    };
    let answer = match &call.ran {
        Ran::Running => small("running".to_owned(), Color::Muted),
        Ran::Answered { bytes, head } => v_flex()
            .child(lines(head, Color::Default))
            .when(*bytes > head.len(), |col| {
                col.child(small(
                    format!("{} more", size_of(bytes.saturating_sub(head.len()))),
                    Color::Muted,
                ))
            })
            .into_any_element(),
        Ran::Failed(why) => lines(why, Color::Error),
        Ran::TimedOut => small(
            "it ran past its deadline and answered nothing".to_owned(),
            Color::Error,
        ),
        Ran::Cancelled => small(
            "the turn stopped before it answered".to_owned(),
            Color::Muted,
        ),
    };
    let colors = cx.theme().colors();
    v_flex()
        .id(("chat-call-details", call.entry))
        .ml(px(18.0))
        .mr_2()
        .mb_1()
        .p_2()
        .gap_1()
        .rounded_sm()
        .border_1()
        .border_color(colors.border_variant)
        .bg(colors.editor_background)
        .overflow_x_scroll()
        .child(small("arguments".to_owned(), Color::Muted))
        .child(lines(&call.args, Color::Muted))
        .child(small("answer".to_owned(), Color::Muted))
        .child(answer)
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Block, blocks, spans};

    /// A reply splits into text and fenced code, and a fence still open runs to the end.
    #[test]
    fn a_reply_splits_into_text_and_code() {
        let said = "It calls\n```c\nint main(void);\n```\nthen returns.\n```\nopen";
        assert_eq!(
            blocks(said),
            [
                Block::Text("It calls"),
                Block::Code(vec!["int main(void);"]),
                Block::Text("then returns."),
                Block::Code(vec!["open"]),
            ]
        );
    }

    /// Code spans lose their backticks and are found where they land; a lone backtick stays.
    #[test]
    fn code_spans_are_found_and_lone_backticks_stay() {
        let (text, ranges) = spans("call `crt_startup` at `0x10` then ` alone");
        assert_eq!(text, "call crt_startup at 0x10 then ` alone");
        assert_eq!(ranges, [5..16, 20..24]);
    }
}
