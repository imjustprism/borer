//! How the chat panel draws: its header, the thread's entries as a document, the bars above
//! the input, the input, and the empty state.
//!
//! A model's reply is drawn from its text written out ([`text::visible`]): fenced code and
//! code spans in the editor's font, everything else as plain text, so nothing in it hides,
//! links or loads from anywhere.

use std::ops::Range;

use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, AppContext as _, Context, ElementId, HighlightStyle, InteractiveElement as _,
    IntoElement, ParentElement as _, SharedString, StatefulInteractiveElement as _, Styled as _,
    StyledText, div, px,
};
use theme_settings::ThemeSettings;
use ui::{
    ActiveTheme as _, Banner, Button, ButtonCommon as _, ButtonLike, ButtonSize, ButtonStyle,
    Clickable as _, Color, CommonAnimationExt as _, CopyButton, Disableable as _, Disclosure,
    FixedWidth as _, Icon, IconButton, IconName, IconSize, Indicator, Label, LabelCommon as _,
    LabelSize, PopoverMenu, Severity, StyledTypography as _, TintColor, Tooltip, h_flex, v_flex,
};

use borer_engine::text;
use settings::Settings as _;

use super::picker::ChatPicker;
use super::thread::{Arg, Call, Chosen, Entry, FENCE_CLOSE, FENCE_OPEN, Fault, HEAD_BYTES, Ran};
use super::{ChatPanel, NewChatThread, PickChatModel, StopChat};
use crate::code_view::{CodePalette, Role};

/// Debug selector of the header, for layout tests.
pub(crate) const HEADER_SELECTOR: &str = "chat-header";

/// Debug selector of the header's line saying where requests go, for layout tests.
pub(crate) const HINT_SELECTOR: &str = "chat-header-hint";

/// Debug selector of an opened tool call's box, for layout tests.
pub(crate) const DETAILS_SELECTOR: &str = "chat-call-details";

/// Debug selector of an opened tool call's input lines, for layout tests.
pub(crate) const INPUT_SELECTOR: &str = "chat-call-input";

/// Debug selector of the held message's Don't Send button, for layout tests.
pub(crate) const DONT_SEND_SELECTOR: &str = "chat-dont-send";

/// Debug selector of the held message's Send button, for layout tests.
pub(crate) const SEND_SELECTOR: &str = "chat-send-held";

/// Debug selector of a code block's lines, the part that scrolls sideways, for layout tests.
pub(crate) const CODE_SELECTOR: &str = "chat-code-lines";

/// The debug selector of a block that scrolls sideways, its scrollbar's track included.
pub(crate) const SIDEWAYS_SELECTOR: &str = "chat-sideways";

/// Debug selector of an opened tool call's Output heading, for layout tests.
pub(crate) const OUTPUT_SELECTOR: &str = "chat-call-output";

/// Most lines of a tool call's input an opened call shows; the rest are counted.
pub(crate) const INPUT_LINES: usize = 6;

/// Most bytes of a code block a reply colors; a longer block is drawn plain.
pub(crate) const CODE_COLORED: usize = 4096;

/// Three questions a reverse engineer asks first of an open binary.
pub(crate) const EXAMPLES: [&str; 3] = [
    "What does this binary do, and which functions should I read first?",
    "How does it read its command line and settings?",
    "Is anything packed, encrypted or checking for a debugger?",
];

/// One block of a reply: running text, or a fenced code block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Block<'a> {
    /// Running text, which may hold code spans.
    Text(&'a str),
    /// A fenced code block: its fence's info string, trimmed, and its lines without the
    /// fences.
    Code(&'a str, Vec<&'a str>),
}

/// Returns `text` split into running text and fenced code blocks; an unclosed fence runs to
/// the end, as a reply still streaming has it.
#[must_use]
pub(crate) fn blocks(text: &str) -> Vec<Block<'_>> {
    let mut blocks = Vec::new();
    let (mut code, mut start, mut at) = (None::<(&str, Vec<&str>)>, 0, 0);
    for line in text.split_inclusive('\n') {
        let fence = line.trim_start().starts_with("```");
        match (&mut code, fence) {
            (None, true) => {
                let before = text.get(start..at).unwrap_or_default().trim_matches('\n');
                if !before.trim().is_empty() {
                    blocks.push(Block::Text(before));
                }
                code = Some((line.trim().trim_start_matches('`').trim(), Vec::new()));
            }
            (Some((lang, lines)), true) => {
                blocks.push(Block::Code(lang, std::mem::take(lines)));
                code = None;
                start = at.saturating_add(line.len());
            }
            (Some((_, lines)), false) => lines.push(line.trim_end_matches(['\n', '\r'])),
            (None, false) => {}
        }
        at = at.saturating_add(line.len());
        if code.is_none() && fence {
            start = at;
        }
    }
    match code {
        Some((lang, lines)) => blocks.push(Block::Code(lang, lines)),
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

/// Returns the icon of the tool `name` by its catalog row, as Zed's agent panel draws a
/// tool's kind: one that only reads, one that proposes edits, or one the catalog does not
/// have.
fn icon_of(name: &str) -> IconName {
    match borer_front::tools::tool(name).map(|t| t.hints.read_only) {
        Some(true) => IconName::ToolSearch,
        Some(false) => IconName::ToolPencil,
        None => IconName::ToolHammer,
    }
}

/// The color runs of each line of one code block: each run's bytes in its line and role.
pub(crate) type Runs = Vec<Vec<(Range<usize>, Role)>>;

/// The color runs of each code block of a text, by block; `None` for a block drawn plain.
pub(crate) type Colors = Vec<Option<Runs>>;

#[cfg(test)]
thread_local! {
    /// How many code blocks [`code_runs`] read on this thread, for the tests that a finished
    /// block is read once.
    pub(crate) static LEXED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Returns the color runs of each line of a code block whose fence says `lang`.
///
/// The runs are the engine's reading of C from the text alone
/// ([`borer_engine::view::c_kinds`]) by the code view's roles, for a block tagged C or C++
/// of at most [`CODE_COLORED`] bytes.
///
/// # Arguments
///
/// * `lang` - The fence's info string; its first word names the language.
/// * `lines` - The block's lines.
///
/// # Returns
///
/// The runs, or `None` for any other block, which is drawn plain.
pub(crate) fn code_runs(lang: &str, lines: &[&str]) -> Option<Runs> {
    let tag = lang.split_whitespace().next().unwrap_or_default();
    let c = ["c", "cpp", "c++", "cc", "h", "hpp"]
        .iter()
        .any(|t| t.eq_ignore_ascii_case(tag));
    let size = lines
        .iter()
        .map(|l| l.len().saturating_add(1))
        .sum::<usize>();
    if !c || size > CODE_COLORED {
        return None;
    }
    #[cfg(test)]
    LEXED.with(|n| n.set(n.get().saturating_add(1)));
    Some(
        lines
            .iter()
            .map(|line| {
                borer_engine::view::c_kinds(line)
                    .into_iter()
                    .filter_map(|(span, kind)| Some((span, Role::of(kind, None)?)))
                    .collect()
            })
            .collect(),
    )
}

/// Returns how many of `said`'s code blocks are closed: a reply still streaming may end
/// inside one, which [`blocks`] runs to the end.
///
/// # Arguments
///
/// * `said` - The text, written out ([`text::visible`]).
pub(crate) fn closed_code_blocks(said: &str) -> usize {
    said.lines()
        .filter(|line| line.trim_start().starts_with("```"))
        .count()
        / 2
}

/// Returns the color runs of each code block of `said` ([`code_runs`]), as a finished
/// entry keeps them so they are read once.
///
/// # Arguments
///
/// * `said` - The entry's text, written out ([`text::visible`]).
pub(crate) fn text_colors(said: &str) -> Colors {
    blocks(said)
        .into_iter()
        .filter_map(|block| match block {
            Block::Code(lang, lines) => Some(code_runs(lang, &lines)),
            Block::Text(_) => None,
        })
        .collect()
}

/// Returns a text button as every one of the chat's is drawn: one size, so one height and
/// one inset on each side of its label and key hint, in `style`.
///
/// # Arguments
///
/// * `id` - The button's element id.
/// * `label` - What it says.
/// * `style` - [`ButtonStyle::Tinted`] for the primary action, [`ButtonStyle::Outlined`]
///   for another.
pub(crate) fn text_button(
    id: impl Into<ElementId>,
    label: impl Into<SharedString>,
    style: ButtonStyle,
) -> Button {
    Button::new(id, label)
        .size(ButtonSize::Medium)
        .label_size(LabelSize::Small)
        .style(style)
}

/// Returns a callout of the thread: `said` on full-width lines, and its buttons under it,
/// left-aligned with the text.
///
/// # Arguments
///
/// * `severity` - How it is colored and which icon it takes.
/// * `said` - What it says.
/// * `buttons` - Its actions, the safe one first and the committing one last, each with
///   the debug selector a layout test finds it by.
fn banner(
    severity: Severity,
    said: String,
    buttons: Vec<(&'static str, Button)>,
) -> impl IntoElement {
    let row = (!buttons.is_empty()).then(|| {
        h_flex().flex_wrap().gap_1().children(
            buttons
                .into_iter()
                .map(|(tag, button)| div().debug_selector(move || tag.to_owned()).child(button)),
        )
    });
    div().px_2().child(
        Banner::new().severity(severity).wrap_content(true).child(
            v_flex()
                .w_full()
                .gap_1p5()
                .child(Label::new(said).size(LabelSize::Small))
                .children(row),
        ),
    )
}

/// Returns whether `text` is a message the input can send: anything but whitespace.
///
/// # Arguments
///
/// * `text` - What the input holds.
pub(crate) fn sendable(text: &str) -> bool {
    !text.trim().is_empty()
}

/// Returns the note under an opened call's input saying what of it is not shown.
///
/// It counts the lines past the ones shown on the input before its cut, one in the
/// singular, and says when the input was cut at [`HEAD_BYTES`], since the last line shown
/// is then not whole.
///
/// # Arguments
///
/// * `call` - The call.
///
/// # Returns
///
/// `1 more line`, `N more lines`, either with `, cut at 2.0 KB`, the cut alone, or `None`
/// when the input shows whole.
pub(crate) fn input_note(call: &Call) -> Option<String> {
    let shown = call.args.lines().take(INPUT_LINES).count();
    let more = match call.arg_lines.saturating_sub(shown) {
        0 => None,
        1 => Some("1 more line".to_owned()),
        n => Some(format!("{n} more lines")),
    };
    let cut = (call.arg_bytes > call.args.len()).then(|| format!("cut at {}", size_of(HEAD_BYTES)));
    match (more, cut) {
        (Some(more), Some(cut)) => Some(format!("{more}, {cut}")),
        (more, cut) => more.or(cut),
    }
}

/// Returns `content` in a block that scrolls sideways under the stable `id`, with Zed's
/// scrollbar shown while it scrolls.
///
/// The scrollbar has a track of its own under the last line when the content is wider
/// than the block, and no track when it is not.
///
/// # Arguments
///
/// * `id` - The block's id, the same every frame, which keeps its scroll.
/// * `content` - What it holds, its lines never wrapped.
/// * `track` - The track's color: the block's background.
/// * `window` - Window it is drawn in.
/// * `cx` - App context.
fn sideways(
    id: impl Into<ElementId>,
    content: impl IntoElement,
    track: gpui::Hsla,
    window: &mut gpui::Window,
    cx: &mut gpui::App,
) -> gpui::Stateful<gpui::Div> {
    ui::WithScrollbar::custom_scrollbars(
        h_flex()
            .debug_selector(|| SIDEWAYS_SELECTOR.to_owned())
            .w_full()
            .items_start()
            .child(div().flex_none().min_w_full().child(content)),
        ui::Scrollbars::new(ui::ScrollAxes::Horizontal)
            .id(id)
            .with_track_along(ui::ScrollAxes::Horizontal, track),
        window,
        cx,
    )
}

impl ChatPanel {
    /// Returns the header: the picker's button with where it sends, the thread's state as
    /// a dot, and New Thread; where it sends goes under the button when both do not fit,
    /// and is never cut.
    pub(super) fn header(&self, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let thread = self.thread.read(cx);
        let chosen = thread.chosen();
        let label = chosen.map_or_else(
            || "Pick a model".to_owned(),
            |c| text::visible(&c.model.name.0).into_owned(),
        );
        let provider = chosen.map_or("No model picked", |c| c.endpoint.offered.label());
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
            .trigger_with_tooltip(
                Button::new("chat-pick", label)
                    .style(ButtonStyle::Subtle)
                    .label_size(LabelSize::Small)
                    .truncate(true)
                    .start_icon(chosen.map(|c| {
                        Icon::new(c.endpoint.offered.icon())
                            .size(IconSize::Small)
                            .color(Color::Muted)
                    }))
                    .end_icon(
                        Icon::new(IconName::ChevronDown)
                            .size(IconSize::XSmall)
                            .color(Color::Muted),
                    ),
                Tooltip::text(provider),
            )
            .with_handle(self.picker.clone())
            .anchor(gpui::Anchor::TopLeft)
            .offset(gpui::point(px(0.0), px(2.0)));
        let hint = hint.map(|hint| {
            div()
                .min_w_0()
                .py_2()
                .debug_selector(|| HINT_SELECTOR.to_owned())
                .child(Label::new(hint).size(LabelSize::Small).color(Color::Muted))
        });
        h_flex()
            .min_h_8()
            .flex_none()
            .items_start()
            .pl_1()
            .pr_1()
            .gap_1()
            .border_b_1()
            .border_color(cx.theme().colors().border_variant)
            .debug_selector(|| HEADER_SELECTOR.to_owned())
            .child(
                h_flex()
                    .min_w_0()
                    .flex_1()
                    .flex_wrap()
                    .gap_x_1()
                    .child(div().min_w_0().py_1().child(picker))
                    .children(hint),
            )
            .child(
                div()
                    .id("chat-status")
                    .h_8()
                    .flex()
                    .items_center()
                    .px_1()
                    .tooltip(Tooltip::text(said))
                    .child(Indicator::dot().color(dot)),
            )
            .child(
                div().h_8().flex().items_center().child(
                    IconButton::new("chat-new-thread", IconName::Plus)
                        .icon_size(IconSize::Small)
                        .tooltip(Tooltip::for_action_title("New Thread", &NewChatThread))
                        .on_click(cx.listener(|this, _, _, cx| {
                            this.thread.update(cx, super::thread::Thread::clear);
                        })),
                ),
            )
    }

    /// Returns entry `ix` of the thread as the person sees it.
    ///
    /// # Arguments
    ///
    /// * `ix` - The entry's index in the thread.
    /// * `window` - Window it is drawn in.
    /// * `cx` - Panel context.
    pub(super) fn entry(
        &self,
        ix: usize,
        window: &mut gpui::Window,
        cx: &mut Context<'_, Self>,
    ) -> AnyElement {
        let thread = self.thread.read(cx);
        let Some(entry) = thread.entries().get(ix) else {
            return div().into_any_element();
        };
        let turn_start = ix > 0 && matches!(entry, Entry::Person(_));
        let kept = self.colors.get(&ix).or_else(|| {
            self.streamed
                .as_ref()
                .filter(|(at, _)| *at == ix)
                .map(|(_, kept)| kept)
        });
        let body = match entry {
            Entry::Person(_) => {
                self.thread
                    .update(cx, |thread, cx| match thread.entries().get(ix) {
                        Some(Entry::Person(said)) => {
                            person(ix, &text::visible(said), kept, window, cx)
                        }
                        _ => div().into_any_element(),
                    })
            }
            Entry::Model(_) => {
                let first = !thread
                    .entries()
                    .get(..ix)
                    .unwrap_or_default()
                    .iter()
                    .rev()
                    .take_while(|e| !matches!(e, Entry::Person(_)))
                    .any(|e| matches!(e, Entry::Model(_)));
                let author = first
                    .then(|| {
                        let chosen = thread.chosen()?;
                        let name = text::visible(&chosen.model.name.0).into_owned();
                        Some(SharedString::from(name))
                    })
                    .flatten();
                self.thread
                    .update(cx, |thread, cx| match thread.entries().get(ix) {
                        Some(Entry::Model(said)) => model(ix, said, author, kept, window, cx),
                        _ => div().into_any_element(),
                    })
            }
            Entry::Tool(_) => match thread.call_at(ix).cloned() {
                Some(call) => self.tool(&call, window, cx),
                None => div().into_any_element(),
            },
            Entry::Notice(said) => {
                let held = thread
                    .held_notice()
                    .is_some_and(|n| std::ptr::eq(n, said.as_str()));
                if held {
                    div().into_any_element()
                } else {
                    quiet(&text::visible(said))
                }
            }
            Entry::Error(said) => {
                let said = text::visible(said).into_owned();
                self.error(ix, &said, cx)
            }
            Entry::Proposal(id) => self.card(*id, cx),
        };
        div()
            .pt_2()
            .when(turn_start, |d| d.pt_6())
            .child(body)
            .into_any_element()
    }

    /// Returns the row of a tool call: its tool, what it reads, its state, and once opened
    /// its arguments and the first lines of its answer.
    ///
    /// # Arguments
    ///
    /// * `call` - The call.
    /// * `window` - Window it is drawn in.
    /// * `cx` - Panel context.
    fn tool(
        &self,
        call: &Call,
        window: &mut gpui::Window,
        cx: &mut Context<'_, Self>,
    ) -> AnyElement {
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
                .size(IconSize::Small)
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
            .h_7()
            .px_2()
            .gap_1p5()
            .rounded_md()
            .cursor_pointer()
            .hover(|s| s.bg(cx.theme().colors().ghost_element_hover))
            .on_click(cx.listener(move |this, _, _, cx| this.toggle_call(ix, cx)))
            .child(
                Icon::new(icon_of(&call.name))
                    .size(IconSize::Small)
                    .color(Color::Muted),
            )
            .child(
                div().min_w_0().flex_shrink_0().max_w_1_2().child(
                    Label::new(text::visible(&call.name).into_owned())
                        .size(LabelSize::Small)
                        .color(Color::Muted)
                        .truncate(),
                ),
            )
            .children(key)
            .child(div().flex_1())
            .child(div().flex_none().child(state))
            .child(
                Disclosure::new(("chat-call-open", ix), open)
                    .opened_icon(IconName::ChevronUp)
                    .closed_icon(IconName::ChevronDown)
                    .on_click(cx.listener(move |this, _, _, cx| this.toggle_call(ix, cx))),
            );
        v_flex()
            .px_2()
            .child(row)
            .when(open, |col| col.child(details(call, window, cx)))
            .into_any_element()
    }

    /// Returns an error the thread shows: quietly when it is a receipt, else as a callout
    /// with the one action that helps.
    fn error(&self, ix: usize, said: &str, cx: &mut Context<'_, Self>) -> AnyElement {
        let thread = self.thread.read(cx);
        let fix = |label: &'static str| text_button(("chat-fix", ix), label, ButtonStyle::Outlined);
        let action = match thread.fault_at(ix) {
            Some(Fault::Stopped) => return quiet(said),
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
        banner(
            Severity::Error,
            said.to_owned(),
            action.map(|b| ("chat-fix", b)).into_iter().collect(),
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
        let waits = thread.head().map(|_| Self::waits(waiting, cx));
        let notice = thread.held_notice().map(|said| {
            let said = text::visible(said).into_owned();
            let dont = text_button("chat-dont-send", "Don't Send", ButtonStyle::Outlined).on_click(
                cx.listener(|this, _, _, cx| {
                    this.thread.update(cx, super::thread::Thread::decline);
                }),
            );
            let send = text_button(
                "chat-send-held",
                "Send",
                ButtonStyle::Tinted(TintColor::Accent),
            )
            .on_click(cx.listener(|this, _, _, cx| {
                this.thread.update(cx, super::thread::Thread::agree);
            }));
            let buttons = vec![(DONT_SEND_SELECTOR, dont), (SEND_SELECTOR, send)];
            div().pt_2().child(banner(Severity::Warning, said, buttons))
        });
        let error = self.error.clone().map(|e| {
            let pick = text_button("chat-error-pick", "Pick a model", ButtonStyle::Outlined)
                .on_click(cx.listener(|this, _, window, cx| this.picker.show(window, cx)));
            div().pt_2().child(banner(
                Severity::Error,
                e.to_string(),
                vec![("chat-error-pick", pick)],
            ))
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

    /// Returns the bar that says how many proposals wait, with the button that shows the
    /// oldest one's card; `waiting` counts those still waiting for a verdict.
    fn waits(waiting: usize, cx: &Context<'_, Self>) -> impl IntoElement {
        let said = match waiting {
            0 => "1 proposal needs you".to_owned(),
            1 => "1 proposal waits for you".to_owned(),
            n => format!("{n} proposals wait for you"),
        };
        h_flex()
            .flex_wrap()
            .justify_between()
            .min_h_8()
            .px_4()
            .py_1()
            .gap_x_2()
            .gap_y_1()
            .child(Label::new(said).size(LabelSize::Small))
            .child(
                text_button("chat-waits", "Review", ButtonStyle::Outlined)
                    .on_click(cx.listener(|this, _, window, cx| this.show_head(window, cx))),
            )
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
                .style(ButtonStyle::Tinted(TintColor::Error))
                .tooltip(Tooltip::for_action_title("Stop", &StopChat))
                .on_click(cx.listener(|this, _, _, cx| {
                    this.thread.update(cx, super::thread::Thread::stop);
                }))
        } else {
            let idle = reason.is_some() || !self.sendable;
            IconButton::new("chat-send", IconName::ArrowUp)
                .icon_size(IconSize::Small)
                .style(ButtonStyle::Filled)
                .icon_color(if idle { Color::Muted } else { Color::Accent })
                .disabled(idle)
                .tooltip(Tooltip::for_action_title("Send", &menu::Confirm))
                .on_click(cx.listener(|this, _, window, cx| this.send(window, cx)))
        };
        let hint = match reason {
            Some(reason) => div()
                .id("chat-pick-hint")
                .px_1()
                .cursor_pointer()
                .hover(|s| s.underline())
                .tooltip(Tooltip::for_action_title("Pick a Model", &PickChatModel))
                .on_click(cx.listener(|this, _, window, cx| this.picker.show(window, cx)))
                .child(small(reason.to_owned(), Color::Muted))
                .into_any_element(),
            None => div()
                .px_1()
                .child(small(
                    "Enter sends \u{b7} Shift+Enter breaks a line".to_owned(),
                    Color::Muted,
                ))
                .into_any_element(),
        };
        let border = if reason.is_some() {
            colors.border_variant
        } else {
            colors.border
        };
        div().flex_none().p_2().child(
            v_flex()
                .rounded_lg()
                .border_1()
                .border_color(border)
                .bg(colors.editor_background)
                .child(div().px_2().pt_2().pb_1().child(self.input.clone()))
                .child(
                    h_flex()
                        .pl_1p5()
                        .pr_2()
                        .pb_1()
                        .gap_1()
                        .child(div().min_w_0().flex_1().child(hint))
                        .child(button),
                ),
        )
    }

    /// Returns what an empty thread shows: what the chat does, and three questions to ask
    /// as plain lines, each sent by a click; dimmed and inert while no model is picked.
    pub(super) fn empty_state(&self, file: &str, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let can = self.thread.read(cx).chosen().is_some();
        let colors = cx.theme().colors();
        let asks = EXAMPLES.iter().enumerate().map(|(n, ask)| {
            let group = SharedString::from(format!("chat-example-{n}"));
            let line = div()
                .text_ui_sm(cx)
                .text_color(if can {
                    colors.text_muted
                } else {
                    colors.text_disabled
                })
                .when(can, |line| {
                    line.group_hover(group.clone(), |s| s.text_color(colors.text))
                })
                .child(*ask);
            ButtonLike::new(("chat-example", n))
                .style(ButtonStyle::Transparent)
                .full_width()
                .auto_height()
                .disabled(!can)
                .on_click(cx.listener(move |this, _, _, cx| {
                    this.thread
                        .update(cx, |t, cx| t.send((*ask).to_owned(), cx));
                }))
                .child(div().group(group).w_full().py_0p5().text_left().child(line))
        });
        v_flex()
            .flex_1()
            .justify_center()
            .px_4()
            .child(
                v_flex()
                    .w_full()
                    .max_w_96()
                    .gap_3()
                    .child(
                        v_flex()
                            .gap_1()
                            .child(Label::new(format!("Ask about {file}")).size(LabelSize::Large))
                            .child(
                                Label::new(
                                    "The model reads the binary through borer's tools. Edits it proposes wait for you.",
                                )
                                .size(LabelSize::Small)
                                .color(Color::Muted),
                            ),
                    )
                    .child(v_flex().w_full().children(asks)),
            )
    }
}

/// Returns the line that says `who` is answering, with a spinner.
fn working(who: &str) -> AnyElement {
    h_flex()
        .h_7()
        .px_4()
        .gap_1p5()
        .child(
            Icon::new(IconName::LoadCircle)
                .size(IconSize::Small)
                .color(Color::Muted)
                .with_rotate_animation(2),
        )
        .child(small(format!("{who} is answering"), Color::Muted))
        .into_any_element()
}

/// Returns a small label in `color`.
fn small(text: String, color: Color) -> AnyElement {
    Label::new(text)
        .size(LabelSize::Small)
        .color(color)
        .into_any_element()
}

/// Returns a quiet line of the thread: muted text.
fn quiet(said: &str) -> AnyElement {
    div()
        .px_4()
        .child(
            Label::new(said.to_owned())
                .size(LabelSize::Small)
                .color(Color::Muted),
        )
        .into_any_element()
}

/// Returns what the person wrote, in a raised block as Zed's agent panel sets a message.
///
/// # Arguments
///
/// * `ix` - The entry's index in the thread.
/// * `said` - What the person wrote, written out ([`text::visible`]).
/// * `kept` - The color runs kept for its code blocks ([`text_colors`]).
/// * `window` - Window it is drawn in.
/// * `cx` - App context.
fn person(
    ix: usize,
    said: &str,
    kept: Option<&Colors>,
    window: &mut gpui::Window,
    cx: &mut gpui::App,
) -> AnyElement {
    let body = prose(ix, said, kept, window, cx);
    let colors = cx.theme().colors();
    div()
        .px_2()
        .child(
            div()
                .px_2()
                .py_2()
                .rounded_md()
                .border_1()
                .border_color(colors.border)
                .bg(colors.editor_background)
                .child(body),
        )
        .into_any_element()
}

/// Returns what the model wrote, written out ([`text::visible`]), as running text.
///
/// A reply that opens its turn sits under its model's name. A copy button shows on hover
/// and copies the text as the model wrote it: on the name's line, or under a reply that
/// goes on.
///
/// # Arguments
///
/// * `ix` - The entry's index in the thread.
/// * `said` - What the model wrote, as it wrote it.
/// * `opens` - The model's name when the reply opens its turn.
/// * `kept` - The color runs kept for its code blocks ([`text_colors`]).
/// * `window` - Window it is drawn in.
/// * `cx` - App context.
fn model(
    ix: usize,
    said: &str,
    opens: Option<SharedString>,
    kept: Option<&Colors>,
    window: &mut gpui::Window,
    cx: &mut gpui::App,
) -> AnyElement {
    let body = prose(ix, &text::visible(said), kept, window, cx);
    let group = SharedString::from(format!("chat-model-{ix}"));
    let copy = CopyButton::new(("chat-copy", ix), said.to_owned())
        .icon_size(IconSize::Small)
        .tooltip_label("Copy reply")
        .visible_on_hover(group.clone());
    let row = h_flex().h_5();
    let (top, end) = match opens {
        Some(opens) => (
            Some(
                row.child(
                    div().min_w_0().flex_1().child(
                        Label::new(opens)
                            .size(LabelSize::Small)
                            .color(Color::Muted)
                            .truncate(),
                    ),
                )
                .child(copy),
            ),
            None,
        ),
        None => (None, Some(row.justify_end().child(copy))),
    };
    v_flex()
        .group(group)
        .px_4()
        .gap_1p5()
        .children(top)
        .child(body)
        .children(end)
        .into_any_element()
}

/// Returns `said` as running text and code blocks, code in the editor's font.
///
/// A small C block ([`code_runs`]) takes the theme's syntax colors, from `kept` once the
/// entry is finished, else read now; a code line is never wrapped, and its block scrolls
/// sideways under an id made of the entry and the block's place, the same every frame.
///
/// # Arguments
///
/// * `ix` - The entry's index in the thread.
/// * `said` - Its text, written out ([`text::visible`]).
/// * `kept` - The color runs kept for the entry's closed code blocks ([`text_colors`]).
/// * `window` - Window it is drawn in.
/// * `cx` - App context.
fn prose(
    ix: usize,
    said: &str,
    kept: Option<&Colors>,
    window: &mut gpui::Window,
    cx: &mut gpui::App,
) -> AnyElement {
    let settings = ThemeSettings::get_global(cx);
    let mono = settings.buffer_font.family.clone();
    let colors = cx.theme().colors();
    let (text, span_bg, border, code_bg) = (
        colors.text,
        colors.element_background,
        colors.border_variant,
        colors.editor_background,
    );
    let palette = CodePalette::from_theme(cx.theme());
    let mut code = 0usize;
    let mut parts = Vec::new();
    for block in blocks(said) {
        parts.push(match block {
            Block::Text(said) => {
                let (said, ranges) = spans(said);
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
                        StyledText::new(said)
                            .with_highlights(ranges.into_iter().map(|r| (r, highlight)))
                            .with_font_family_overrides(fonts),
                    )
                    .into_any_element()
            }
            Block::Code(lang, lines) => {
                let read;
                let runs = match kept.and_then(|k| k.get(code)) {
                    Some(runs) => runs.as_ref(),
                    None => {
                        read = code_runs(lang, &lines);
                        read.as_ref()
                    }
                };
                let rows = lines.iter().enumerate().map(|(n, line)| {
                    let styled = StyledText::new((*line).to_owned());
                    let styled = match runs.and_then(|r| r.get(n)) {
                        Some(runs) => styled.with_highlights(runs.iter().map(|(span, role)| {
                            let color = Some(palette.color(*role));
                            let style = HighlightStyle {
                                color,
                                ..HighlightStyle::default()
                            };
                            (span.clone(), style)
                        })),
                        None => styled,
                    };
                    div().child(styled)
                });
                let id = SharedString::from(format!("chat-code-{ix}-{code}"));
                code = code.saturating_add(1);
                let body = v_flex()
                    .debug_selector(|| CODE_SELECTOR.to_owned())
                    .px_2()
                    .py_1p5()
                    .font_family(mono.clone())
                    .text_ui_sm(cx)
                    .whitespace_nowrap()
                    .children(rows);
                div()
                    .rounded_md()
                    .border_1()
                    .border_color(border)
                    .bg(code_bg)
                    .overflow_hidden()
                    .child(sideways(id, body, code_bg, window, cx))
                    .into_any_element()
            }
        });
    }
    v_flex()
        .gap_2()
        .text_ui(cx)
        .line_height(gpui::relative(1.5))
        .text_color(text)
        .children(parts)
        .into_any_element()
}

/// Returns the first lines of a tool's answer without the fence the model reads it in
/// ([`FENCE_OPEN`], [`FENCE_CLOSE`]): the person's view marks the data by its label instead.
///
/// The fence is only ever the answer's first and last line, since [`super::thread::fenced`]
/// writes every `<` inside it as a character reference: so a head cut inside the closing
/// fence ends on a start of it, which is dropped too.
pub(crate) fn unfenced(head: &str) -> &str {
    let body = head.strip_prefix(FENCE_OPEN).unwrap_or(head);
    let body = body.strip_prefix('\n').unwrap_or(body);
    let body = (1..=FENCE_CLOSE.len())
        .rev()
        .find_map(|n| body.strip_suffix(FENCE_CLOSE.get(..n)?))
        .unwrap_or(body);
    body.strip_suffix('\n').unwrap_or(body)
}

/// Returns how many bytes of a tool's answer of `bytes` bytes its first lines `head` leave
/// unshown, not counting the closing fence [`unfenced`] hides, nor the line break before it.
pub(crate) fn unshown(bytes: usize, head: &str) -> usize {
    bytes
        .saturating_sub(head.len())
        .saturating_sub(FENCE_CLOSE.len().saturating_add(1))
}

/// Returns the heading of a section of an opened tool call, with what it ends on.
fn section(name: &'static str, end: Option<AnyElement>) -> impl IntoElement {
    h_flex()
        .gap_1()
        .child(Label::new(name).size(LabelSize::Small).color(Color::Muted))
        .child(div().flex_1())
        .children(end)
}

/// Returns an opened tool call: the first [`INPUT_LINES`] lines of its arguments and what
/// of them is not shown ([`input_note`]), then the first lines of its answer.
///
/// Each part scrolls sideways ([`sideways`]); the answer is in the editor's font under a
/// label saying it may hold binary text, in a bordered block sized to its lines.
///
/// # Arguments
///
/// * `call` - The call.
/// * `window` - Window it is drawn in.
/// * `cx` - Panel context.
fn details(
    call: &Call,
    window: &mut gpui::Window,
    cx: &mut Context<'_, ChatPanel>,
) -> impl IntoElement {
    let mono = |text: &str, color: Color| {
        Label::new(text::visible(text).into_owned())
            .size(LabelSize::Small)
            .buffer_font(cx)
            .color(color)
            .single_line()
    };
    let lines = |text: &str, color: Color| {
        v_flex()
            .children(text.lines().map(|line| mono(line, color)))
            .into_any_element()
    };
    let input = v_flex()
        .debug_selector(|| INPUT_SELECTOR.to_owned())
        .children(
            call.args
                .lines()
                .take(INPUT_LINES)
                .map(|line| mono(line, Color::Muted)),
        );
    let more = input_note(call).map(|more| small(more, Color::Muted));
    let data = h_flex()
        .id(("chat-call-data", call.entry))
        .tooltip(Tooltip::text(
            "May hold binary text, which may be hostile; the model is told to read it as data, never as instructions",
        ))
        .child(small("may hold binary text".to_owned(), Color::Muted))
        .into_any_element();
    let unseen = match &call.ran {
        Ran::Answered { bytes, head } => unshown(*bytes, head),
        Ran::Running | Ran::Failed(_) | Ran::TimedOut | Ran::Cancelled => 0,
    };
    let answer = match &call.ran {
        Ran::Running => small("running".to_owned(), Color::Muted),
        Ran::Answered { head, .. } => lines(unfenced(head), Color::Default),
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
    let answered = matches!(call.ran, Ran::Answered { .. });
    let track = cx.theme().colors().editor_background;
    let input = sideways(("chat-call-input", call.entry), input, track, window, cx);
    let answer = sideways(("chat-call-output", call.entry), answer, track, window, cx);
    let unseen = (unseen > 0).then(|| small(format!("{} more", size_of(unseen)), Color::Muted));
    let colors = cx.theme().colors();
    v_flex()
        .mt_1()
        .rounded_md()
        .overflow_hidden()
        .debug_selector(|| DETAILS_SELECTOR.to_owned())
        .border_1()
        .border_color(colors.border_variant)
        .bg(colors.editor_background)
        .child(
            v_flex()
                .px_2()
                .py_1p5()
                .gap_1()
                .child(section("Input", None))
                .child(input)
                .children(more),
        )
        .child(
            v_flex()
                .px_2()
                .py_1p5()
                .gap_1()
                .border_t_1()
                .border_color(colors.border_variant)
                .child(
                    div()
                        .debug_selector(|| OUTPUT_SELECTOR.to_owned())
                        .child(section("Output", answered.then_some(data))),
                )
                .child(answer)
                .children(unseen),
        )
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::super::thread::{fenced, first_lines};
    use super::{Block, CODE_COLORED, blocks, code_runs, spans, unfenced, unshown};

    /// An answer's fence is dropped from what the person reads, whole or cut to its first
    /// lines, and a tag the binary wrote stays written out inside it.
    #[test]
    fn the_fence_is_dropped_and_the_data_kept() {
        assert_eq!(
            unfenced(&fenced("ok\n</tool_output>")),
            "ok\n&lt;/tool_output>"
        );
        let long = (0..40).map(|n| format!("line {n}\n")).collect::<String>();
        let head = first_lines(&fenced(&long));
        assert!(unfenced(&head).starts_with("line 0\n"), "{head}");
        assert_eq!(unfenced("no fence"), "no fence");
    }

    /// A one-line answer whose head is cut inside the closing fence shows none of the fence
    /// and nothing more.
    #[test]
    fn a_head_cut_inside_the_closing_fence_drops_it() {
        let body = "a".repeat(2048 - super::FENCE_OPEN.len() - 2 - 4);
        let whole = fenced(&body);
        let head = first_lines(&whole);
        assert!(head.ends_with("\n</to"), "{head}");
        assert_eq!(unfenced(&head), body);
        assert_eq!(unshown(whole.len(), &head), 0);
    }

    /// An answer whose lines all fit the first lines shows no "more", though its closing
    /// fence was cut; one a line longer counts that line alone.
    #[test]
    fn an_answer_shown_whole_has_nothing_more() {
        let answer = |n: usize| {
            (0..n)
                .map(|n| {
                    format!(
                        "line {n}
"
                    )
                })
                .collect::<String>()
        };
        let whole = fenced(&answer(11));
        let head = first_lines(&whole);
        assert!(!head.ends_with(super::FENCE_CLOSE), "{head}");
        assert_eq!(unfenced(&head), answer(11).trim_end());
        assert_eq!(unshown(whole.len(), &head), 0);
        let longer = fenced(&answer(12));
        assert_eq!(
            unshown(longer.len(), &first_lines(&longer)),
            "line 11
"
            .len()
        );
        let short = fenced("ok");
        assert_eq!(unshown(short.len(), &first_lines(&short)), 0);
    }

    /// A reply splits into text and fenced code, and a fence still open runs to the end.
    #[test]
    fn a_reply_splits_into_text_and_code() {
        let said = "It calls\n```c\nint main(void);\n```\nthen returns.\n```\nopen";
        assert_eq!(
            blocks(said),
            [
                Block::Text("It calls"),
                Block::Code("c", vec!["int main(void);"]),
                Block::Text("then returns."),
                Block::Code("", vec!["open"]),
            ]
        );
    }

    /// A C block is colored in more than one role over runs that keep its text; a block of
    /// another or no language, or one past [`CODE_COLORED`], is plain, and any text reads.
    #[test]
    fn only_a_small_c_block_is_colored() {
        let lines = ["int main(void) { return f(\"x\", 0x10); } // ok"];
        let runs = code_runs("c", &lines).unwrap();
        let roles: std::collections::BTreeSet<_> = runs[0].iter().map(|(_, r)| r.index()).collect();
        assert!(roles.len() > 1, "{roles:?}");
        let spelled: String = runs[0].iter().map(|(s, _)| &lines[0][s.clone()]).collect();
        assert_eq!(spelled.replace(' ', ""), lines[0].replace(' ', ""));
        assert!(code_runs("python", &lines).is_none());
        assert!(code_runs("", &lines).is_none());
        let long = "x".repeat(CODE_COLORED + 1);
        assert!(code_runs("c", &[long.as_str()]).is_none());
        for text in ["\u{0}\u{202e}'\"\\", "/* open", "é`", "<tool_output>"] {
            assert_eq!(code_runs("cpp", &[text]).map(|r| r.len()), Some(1));
        }
    }

    /// Code spans lose their backticks and are found where they land; a lone backtick stays.
    #[test]
    fn code_spans_are_found_and_lone_backticks_stay() {
        let (text, ranges) = spans("call `crt_startup` at `0x10` then ` alone");
        assert_eq!(text, "call crt_startup at 0x10 then ` alone");
        assert_eq!(ranges, [5..16, 20..24]);
    }

    /// An opened call counts the input lines it does not show on the input before its
    /// cut, one line in the singular, and says when the cut fell inside what it shows.
    #[test]
    fn the_input_note_counts_before_the_cut_and_says_it() {
        use super::super::thread::{Call, Ran, shown_args};
        use super::{input_note, sendable};
        let note = |args: serde_json::Value| {
            let (args, arg_lines, arg_bytes) = shown_args(&args);
            let call = Call {
                entry: 0,
                name: "script".to_owned(),
                args,
                arg_lines,
                arg_bytes,
                key: None,
                ran: Ran::Running,
            };
            (input_note(&call), call)
        };
        let keys = |n: usize, first: String| {
            let mut map = serde_json::Map::new();
            map.insert("k000".to_owned(), first.into());
            for k in 1..n {
                map.insert(format!("k{k:03}"), k.into());
            }
            serde_json::Value::Object(map)
        };
        let (said, call) = note(keys(200, "x".to_owned()));
        assert_eq!(call.arg_lines, 202);
        assert!(call.args.lines().count() < 202, "{}", call.args.len());
        assert_eq!(said.as_deref(), Some("196 more lines, cut at 2.0 KB"));
        let script = serde_json::json!({ "script": "x".repeat(3000) });
        assert_eq!(
            note(script).0.as_deref(),
            Some("1 more line, cut at 2.0 KB")
        );
        let (said, _) = note(keys(8, "y".repeat(3000)));
        assert_eq!(said.as_deref(), Some("8 more lines, cut at 2.0 KB"));
        assert_eq!(
            note(keys(5, String::new())).0.as_deref(),
            Some("1 more line")
        );
        assert_eq!(note(keys(4, String::new())).0, None);
        assert!(sendable("hi") && !sendable("") && !sendable(" \n\t"));
    }
}
