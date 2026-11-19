//! The chat's proposal cards: the fields a proposal shows, its title by kind, and the one
//! card the thread draws for it where it was made.
//!
//! Every field is written out ([`text::visible`]) and bounded alone, so no text the binary
//! wrote can push what changes off the card or stand in for it. The oldest proposal that
//! waits ([`super::thread::Thread::head`]) is the only card Accept and Reject reach: it
//! holds the panel's card focus, and while it has focus Enter accepts and Escape rejects.

use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, Context, Focusable as _, InteractiveElement as _, IntoElement, KeyUpEvent,
    MouseButton, ParentElement as _, SharedString, StatefulInteractiveElement as _, Styled as _,
    Window, div, px,
};
use ui::{
    ActiveTheme as _, Button, ButtonCommon as _, ButtonStyle, Clickable as _, Color, Icon,
    IconName, IconSize, KeyBinding, Label, LabelCommon as _, LabelSize, TintColor, h_flex, v_flex,
};

use std::collections::{BTreeMap, BTreeSet};

use borer_engine::analysis::edit::{Change, Line, Plan};
use borer_engine::text;

#[cfg(test)]
use super::thread::Proposal;
use super::thread::Verdict;
use super::{AcceptChatProposal, ChatPanel, RejectChatProposal, shown as shown_text};
use crate::binary::Author;

/// Width of a card's field labels, so the values line up.
const LABEL_WIDTH: f32 = 60.0;

/// What a field of a proposal card states.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// The address a change is made at, which opens its function.
    Address(u64),
    /// The name the address goes by now.
    Now,
    /// The name it takes.
    Becomes,
    /// The comment it takes, whole.
    Comment,
    /// The type a change states.
    Type,
    /// What the person should know before accepting.
    Warning,
    /// A line of the engine's plan, unlabeled.
    Line,
}

impl Kind {
    /// Returns the field's label on the card; empty for a plan line.
    const fn label(self) -> &'static str {
        match self {
            Self::Address(_) => "address",
            Self::Now => "now",
            Self::Becomes => "becomes",
            Self::Comment => "comment",
            Self::Type => "type",
            Self::Warning => "warning",
            Self::Line => "",
        }
    }
}

/// One field of a proposal card.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// What it states.
    pub kind: Kind,
    /// Its value, written out.
    pub value: String,
}

/// Most changes of one plan a card spells out field by field; the rest are counted.
pub const CHANGES_SHOWN: usize = 50;

/// What a proposal card shows of its plan, made once per plan, never per frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Shown {
    /// The fields of the plan's first [`CHANGES_SHOWN`] changes, in order.
    pub fields: Vec<Field>,
    /// How many changes the plan makes in all.
    pub changes: usize,
    /// How many changes of each kind it makes, by the kind's plural noun, in a fixed order.
    pub kinds: Vec<(&'static str, usize)>,
    /// Whether it takes a name another address holds now.
    pub takes: bool,
    /// Its title by what it does ([`title`]).
    pub title: String,
}

/// Returns what a card shows of `plan`: the fields of its first [`CHANGES_SHOWN`] changes,
/// read from what the plan writes, its counts by kind, and whether it takes a held name.
///
/// For a rename the address, the name now and the new name, with a warning when the new
/// name mixes Latin with look-alike letters; for a comment the address and the comment the
/// plan writes there, whole; for a type what it states, and each type a declaration or
/// layout defines.
pub fn shown(plan: &Plan) -> Shown {
    let mut written: BTreeMap<u64, Option<&str>> = BTreeMap::new();
    let mut freed = BTreeSet::new();
    for change in plan.changes() {
        match change {
            Change::Comment(at, swap) => {
                written.insert(*at, swap.after().map(String::as_str));
            }
            Change::Name(_, swap) => {
                if let (Some(old), None) = (swap.before(), swap.after()) {
                    freed.insert(old.as_str());
                }
            }
            Change::Type(..)
            | Change::Applied(..)
            | Change::Proto(..)
            | Change::Var(..)
            | Change::Field(..) => {}
        }
    }
    let lines = plan.lines();
    let mut kinds = [("renames", 0usize), ("comments", 0), ("types", 0)];
    let mut takes = false;
    for line in lines {
        let at = match line {
            Line::Named { new, .. } => {
                takes |= freed.contains(new.as_str());
                0
            }
            Line::Commented { .. } => 1,
            Line::Declared { .. } | Line::Stated { .. } | Line::Unknown(_) | Line::Laid { .. } => 2,
        };
        if let Some(kind) = kinds.get_mut(at) {
            kind.1 = kind.1.saturating_add(1);
        }
    }
    let mut fields = Vec::new();
    for line in lines.iter().take(CHANGES_SHOWN) {
        line_fields(line, &written, &mut fields);
    }
    Shown {
        fields,
        changes: lines.len(),
        kinds: kinds.into_iter().filter(|k| k.1 > 0).collect(),
        takes,
        title: title(lines),
    }
}

/// Adds the fields of one plan line to `fields`; `written` holds the comment the plan
/// writes at each address, `None` where it removes one.
fn line_fields(line: &Line, written: &BTreeMap<u64, Option<&str>>, fields: &mut Vec<Field>) {
    let mut field = |kind, value| fields.push(Field { kind, value });
    match line {
        Line::Named {
            target, old, new, ..
        } => {
            field(Kind::Address(*target), format!("{target:#x}"));
            field(Kind::Now, shown_text(old));
            field(Kind::Becomes, shown_text(new));
            if text::mixes_scripts(new) {
                let warn =
                    "the new name mixes Latin letters with lookalike letters of another script";
                field(Kind::Warning, warn.to_owned());
            }
        }
        Line::Commented { at } => {
            field(Kind::Address(*at), format!("{at:#x}"));
            let said = written.get(at).copied().flatten();
            let said = said.map_or_else(
                || "(removed)".to_owned(),
                |said| text::visible(said).into_owned(),
            );
            field(Kind::Comment, said);
        }
        Line::Stated { would, .. } => field(Kind::Type, shown_text(would)),
        Line::Declared { types, abi, lines } => {
            let noun = if *types == 1 { "type" } else { "types" };
            field(
                Kind::Line,
                format!("{types} {noun} from C, laid out for {abi}"),
            );
            for t in lines {
                field(Kind::Type, shown_text(t));
            }
        }
        Line::Laid {
            name,
            prototypes,
            lines,
        } => {
            let said = format!(
                "struct {}, typing {prototypes} prototypes",
                shown_text(name)
            );
            field(Kind::Line, said);
            for t in lines {
                field(Kind::Type, shown_text(t));
            }
        }
        Line::Unknown(_) => field(Kind::Line, shown_text(&line.said(true).0)),
    }
}

/// Returns each field of `proposal`'s card as one line with its color, as the card reads
/// it: `address 0x...`, then `label: value`.
#[cfg(test)]
pub(crate) fn lines(proposal: &Proposal) -> Vec<(String, Color)> {
    proposal
        .shown
        .fields
        .iter()
        .cloned()
        .map(|f| {
            let line = match f.kind {
                Kind::Address(_) => format!("address {}", f.value),
                Kind::Line => f.value,
                Kind::Now | Kind::Becomes | Kind::Comment | Kind::Type | Kind::Warning => {
                    format!("{}: {}", f.kind.label(), f.value)
                }
            };
            (line, color_of(f.kind))
        })
        .collect()
}

/// Returns the color a field of `kind` is drawn in.
const fn color_of(kind: Kind) -> Color {
    match kind {
        Kind::Address(_) => Color::Accent,
        Kind::Warning => Color::Warning,
        Kind::Now => Color::Muted,
        Kind::Becomes | Kind::Comment | Kind::Type | Kind::Line => Color::Default,
    }
}

/// Returns the card's title by what its plan does.
///
/// It is `Rename function`, `Rename 12 functions`, `Set comment`, `Set type`, `Define
/// types`, `Apply class layout`, or `Script edits` for a plan of several kinds.
fn title(lines: &[Line]) -> String {
    let named = lines
        .iter()
        .filter(|l| matches!(l, Line::Named { .. }))
        .count();
    let functions = lines
        .iter()
        .all(|l| matches!(l, Line::Named { function: true, .. }));
    let one = |what: &str| match lines.len() {
        1 => what.to_owned(),
        n => format!("{what}, {n} changes"),
    };
    match lines.first() {
        Some(Line::Named { .. }) if named == lines.len() => match (named, functions) {
            (1, true) => "Rename function".to_owned(),
            (1, false) => "Rename data".to_owned(),
            (n, true) => format!("Rename {n} functions"),
            (n, false) => format!("Rename {n} names"),
        },
        _ if named > 0 => format!("Script edits, {} changes", lines.len()),
        Some(Line::Commented { .. }) => one("Set comment"),
        Some(Line::Stated { .. } | Line::Unknown(_)) => one("Set type"),
        Some(Line::Declared { .. }) => one("Define types"),
        Some(Line::Laid { .. }) => one("Apply class layout"),
        Some(Line::Named { .. }) | None => "Edit".to_owned(),
    }
}

/// Returns the quiet line a card past its verdict is, naming what it wrote; `None` while it
/// still takes a verdict.
fn receipt(shown: &Shown, verdict: &Verdict) -> Option<AnyElement> {
    let (icon, color, said) = match verdict {
        Verdict::Accepted => {
            let value = shown
                .fields
                .iter()
                .find(|f| matches!(f.kind, Kind::Becomes | Kind::Comment | Kind::Type));
            let said = value.map_or_else(
                || "accepted".to_owned(),
                |f| format!("accepted: {}", f.value),
            );
            (IconName::Check, Color::Success, said)
        }
        Verdict::Rejected => (
            IconName::Close,
            Color::Muted,
            "rejected, nothing written".to_owned(),
        ),
        Verdict::Waiting | Verdict::Accepting | Verdict::Refused(_) | Verdict::Stale => {
            return None;
        }
    };
    Some(
        h_flex()
            .px_2()
            .py_0p5()
            .gap_1p5()
            .child(Icon::new(icon).size(IconSize::XSmall).color(color))
            .child(
                div().min_w_0().flex_1().child(
                    Label::new(format!("{} {said}", shown.title))
                        .size(LabelSize::Small)
                        .color(Color::Muted)
                        .truncate(),
                ),
            )
            .into_any_element(),
    )
}

/// Returns the line that says how much of a large or mixed plan the card spells out:
/// `showing 50 of 1200 changes`, then its counts by kind; `None` for a plan shown whole of
/// one kind.
fn summary(shown: &Shown) -> Option<AnyElement> {
    if shown.changes <= CHANGES_SHOWN && shown.kinds.len() < 2 {
        return None;
    }
    let mut said = if shown.changes > CHANGES_SHOWN {
        format!("showing {CHANGES_SHOWN} of {} changes", shown.changes)
    } else {
        format!("{} changes", shown.changes)
    };
    for (kind, n) in &shown.kinds {
        said.push_str(&format!(" \u{b7} {n} {kind}"));
    }
    Some(
        Label::new(said)
            .size(LabelSize::XSmall)
            .color(Color::Muted)
            .into_any_element(),
    )
}

/// Returns who proposed a change, as its card says.
fn proposed_by(author: &Author) -> String {
    match author {
        Author::Model { provider, model } => format!(
            "proposed by {} \u{b7} {}",
            text::visible(provider),
            text::visible(model)
        ),
        Author::Person => "proposed by you".to_owned(),
    }
}

impl ChatPanel {
    /// Returns the card of proposal `id`, made at entry `ix` of the thread.
    ///
    /// A card past its verdict is one quiet line; one that waits shows its fields, who
    /// proposed it and the buttons its state allows: Accept and Reject while it waits at
    /// the head, the engine's reason and Dismiss once refused, Plan Again and Dismiss once
    /// stale; a card queued behind the head says so and takes no verdict yet.
    pub(super) fn card(&self, id: usize, cx: &mut Context<'_, Self>) -> AnyElement {
        let thread = self.thread.read(cx);
        let Some(proposal) = thread.proposal(id) else {
            return div().into_any_element();
        };
        let head = thread.head() == Some(id);
        let (shown, verdict) = (proposal.shown.clone(), proposal.verdict.clone());
        let author = proposed_by(&proposal.author);
        if let Some(receipt) = receipt(&shown, &verdict) {
            return receipt;
        }
        let colors = cx.theme().colors();
        let border = if head {
            colors.border_focused
        } else {
            colors.border
        };
        let surface = colors.elevated_surface_background;
        let summary = summary(&shown);
        let title = shown.title.clone();
        let force = shown.takes.then(|| {
            Label::new("takes a name another address holds")
                .size(LabelSize::Small)
                .color(Color::Warning)
        });
        let body = Self::card_fields(id, shown.fields, cx);
        let footer = self.card_footer(id, &verdict, head, cx);
        let card = v_flex()
            .id(("chat-card", id))
            .mx_2()
            .my_1()
            .p_2()
            .gap_1p5()
            .rounded_md()
            .border_1()
            .border_color(border)
            .bg(surface)
            .child(
                h_flex()
                    .gap_1p5()
                    .child(
                        Icon::new(IconName::Pencil)
                            .size(IconSize::Small)
                            .color(Color::Muted),
                    )
                    .child(Label::new(title).size(LabelSize::Small))
                    .child(div().flex_1())
                    .child(
                        Label::new(format!("#{}", id.saturating_add(1)))
                            .size(LabelSize::XSmall)
                            .color(Color::Muted),
                    ),
            )
            .children(summary)
            .children(force)
            .child(body)
            .child(
                Label::new(author)
                    .size(LabelSize::XSmall)
                    .color(Color::Muted),
            )
            .child(footer);
        if !head {
            return card.into_any_element();
        }
        let focus = self.card.clone();
        card.key_context("ChatProposal")
            .track_focus(&self.card)
            .on_mouse_down(MouseButton::Left, move |_, window, cx| {
                focus.focus(window, cx);
            })
            .on_action(
                cx.listener(move |this, _: &AcceptChatProposal, window, cx| {
                    this.decide(id, true, window, cx);
                }),
            )
            .on_action(cx.listener(move |this, _: &menu::Confirm, _, _| {
                this.armed = Some(id);
            }))
            .on_key_up(cx.listener(move |this, event: &KeyUpEvent, window, cx| {
                let enter = event.keystroke.key == "enter" && !event.keystroke.modifiers.modified();
                if enter && this.armed.take() == Some(id) {
                    this.decide(id, true, window, cx);
                }
            }))
            .on_action(
                cx.listener(move |this, _: &RejectChatProposal, window, cx| {
                    this.decide(id, false, window, cx);
                }),
            )
            .on_action(cx.listener(move |this, _: &menu::Cancel, window, cx| {
                this.decide(id, false, window, cx);
            }))
            .into_any_element()
    }

    /// Accepts proposal `id` when it waits, or rejects it, then gives the input focus, so
    /// the next card is never decided by the same key: Accept takes no refused or stale
    /// card.
    ///
    /// # Arguments
    ///
    /// * `id` - The proposal.
    /// * `accept` - Whether to accept it rather than reject it.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    pub(super) fn decide(
        &mut self,
        id: usize,
        accept: bool,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.armed = None;
        self.thread.update(cx, |t, cx| {
            let waits = t
                .proposal(id)
                .is_some_and(|p| p.verdict == Verdict::Waiting);
            match (accept, waits) {
                (true, true) => t.accept(id, cx),
                (false, _) => t.reject(id, cx),
                (true, false) => {}
            }
        });
        self.input.focus_handle(cx).focus(window, cx);
    }

    /// Returns the card's fields, each on its own line with its label, values aligned and
    /// wrapping; the address opens its function; a long plan scrolls inside the card.
    fn card_fields(id: usize, fields: Vec<Field>, cx: &mut Context<'_, Self>) -> AnyElement {
        let rows: Vec<_> = fields
            .into_iter()
            .enumerate()
            .map(|(n, f)| {
                let value = Label::new(f.value)
                    .size(LabelSize::Small)
                    .buffer_font(cx)
                    .color(color_of(f.kind));
                let value = match f.kind {
                    Kind::Address(va) => div()
                        .id(SharedString::from(format!("chat-card-at-{id}-{n}")))
                        .cursor_pointer()
                        .hover(|s| s.underline())
                        .on_click(cx.listener(move |this, _, window, cx| {
                            this.open_address(va, window, cx);
                        }))
                        .child(value)
                        .into_any_element(),
                    Kind::Now
                    | Kind::Becomes
                    | Kind::Comment
                    | Kind::Type
                    | Kind::Warning
                    | Kind::Line => div().min_w_0().flex_1().child(value).into_any_element(),
                };
                let gap = matches!(f.kind, Kind::Address(_)) && n > 0;
                h_flex()
                    .items_start()
                    .gap_2()
                    .when(gap, |row| row.mt_1())
                    .child(
                        div().w(px(LABEL_WIDTH)).flex_none().child(
                            Label::new(f.kind.label())
                                .size(LabelSize::XSmall)
                                .color(Color::Muted),
                        ),
                    )
                    .child(value)
            })
            .collect();
        v_flex()
            .id(("chat-card-fields", id))
            .max_h(px(240.0))
            .overflow_y_scroll()
            .children(rows)
            .into_any_element()
    }

    /// Returns the card's last row: its state and the buttons that state allows.
    fn card_footer(
        &self,
        id: usize,
        verdict: &Verdict,
        head: bool,
        cx: &mut Context<'_, Self>,
    ) -> AnyElement {
        let note = |text: String, color: Color| {
            div()
                .min_w_0()
                .flex_1()
                .child(Label::new(text).size(LabelSize::Small).color(color))
        };
        let dismiss = |label: &'static str| {
            Button::new(("chat-dismiss", id), label)
                .style(ButtonStyle::Subtle)
                .label_size(LabelSize::Small)
                .key_binding(
                    KeyBinding::for_action_in(&menu::Cancel, &self.card, cx).size(px(11.0)),
                )
                .on_click(cx.listener(move |this, _, window, cx| {
                    this.decide(id, false, window, cx);
                }))
        };
        let row = h_flex().gap_1().items_center();
        match (verdict, head) {
            (Verdict::Waiting, true) => row
                .child(note(
                    "nothing changes until you accept".to_owned(),
                    Color::Muted,
                ))
                .child(dismiss("Reject"))
                .child(
                    Button::new(("chat-accept", id), "Accept")
                        .style(ButtonStyle::Tinted(TintColor::Accent))
                        .label_size(LabelSize::Small)
                        .key_binding(
                            KeyBinding::for_action_in(&menu::Confirm, &self.card, cx)
                                .size(px(11.0)),
                        )
                        .on_click(cx.listener(move |this, _, window, cx| {
                            this.decide(id, true, window, cx);
                        })),
                )
                .into_any_element(),
            (Verdict::Waiting | Verdict::Refused(_) | Verdict::Stale, false) => row
                .child(note(
                    "waits behind the proposal before it".to_owned(),
                    Color::Muted,
                ))
                .into_any_element(),
            (Verdict::Accepting, _) => row
                .child(note("accepting".to_owned(), Color::Muted))
                .into_any_element(),
            (Verdict::Refused(why), true) => row
                .child(note(
                    format!("refused: {}; nothing was written", shown_text(why)),
                    Color::Error,
                ))
                .child(dismiss("Dismiss"))
                .into_any_element(),
            (Verdict::Stale, true) => row
                .child(note(
                    "the binary changed since it was planned".to_owned(),
                    Color::Warning,
                ))
                .child(dismiss("Dismiss"))
                .child(
                    Button::new(("chat-again", id), "Plan Again")
                        .style(ButtonStyle::Filled)
                        .label_size(LabelSize::Small)
                        .on_click(cx.listener(move |this, _, _, cx| {
                            this.thread.update(cx, |t, cx| t.plan_again(id, cx));
                        })),
                )
                .into_any_element(),
            (Verdict::Accepted | Verdict::Rejected, _) => row.into_any_element(),
        }
    }
}
