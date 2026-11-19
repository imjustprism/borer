//! Annotating in place: an inline editor under the token or row a person annotates.
//!
//! It renames, comments, types or declares: it plans what is typed through the engine's
//! edit path as it is typed and shows the plan's lines, so Enter commits the plan on
//! screen and Escape writes nothing.
//!
//! Which edit a referent takes is the engine's ([`crate::worker::offer_blocking`]), and
//! what is typed plans through the catalog row an agent would call; a refusal is the
//! engine's or the row's sentence, with no word of the app's.

use std::sync::Arc;

use borer_engine::analysis::edit::{Author, Change, Form, Kind, Offer, Plan, open_question};
use borer_engine::text;
use borer_engine::view::Ref;
use editor::{Editor, EditorEvent};
use gpui::TextStyleRefinement;
use gpui::{
    AppContext as _, Context, Entity, EventEmitter, FocusHandle, Focusable, InteractiveElement,
    IntoElement, ParentElement as _, Render, Styled as _, Subscription, Window, div,
};
use settings::Settings as _;
use theme_settings::ThemeSettings;
use ui::{ActiveTheme as _, Color, Label, LabelCommon as _, LabelSize, v_flex};

use workspace::Workspace;

use crate::binary::{Binary, BinaryEvent, Committed, ONE_FILE};
use crate::commands;
use crate::decompile_item::DecompileItem;
use crate::history::Way;
use crate::worker::{
    Job, LoadedBinary, Shown, offer_blocking, plan_form_blocking, read_header_blocking,
    spawn_engine,
};

gpui::actions!(
    borer,
    [
        /// Renames what the cursor or the selected row is on, inline: the engine's plan
        /// shows as the name is typed, Enter commits it.
        Rename,
        /// Comments the line or row the cursor is on, inline, as Rename does.
        Comment,
        /// Asks an open question at the line or row the cursor is on: a comment opening
        /// with `?`.
        AskQuestion,
        /// Types what the cursor is on: a variable, a global, or a function's prototype on
        /// its signature or a call.
        SetType,
        /// Defines types from C declarations typed or pasted in the active code tab.
        DeclareC,
        /// Defines types from the C declarations of a header file picked in the system
        /// dialog.
        DeclareHeader,
        /// Defines an enum, `Name: A = 1, B`.
        NewEnum,
        /// Defines a typedef, `Name = type`.
        NewTypedef,
        /// Takes the newest edit back through the engine's revert.
        UndoEdit,
        /// Puts the newest edit taken back again.
        RedoEdit,
    ]
);

/// What a person asks to do in place.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ask {
    /// A new name.
    Rename,
    /// A comment.
    Comment,
    /// An open question: a comment opening with `?`.
    Question,
    /// A type, or a function's prototype.
    Type,
    /// C declarations.
    Declare,
    /// An enum.
    Enum,
    /// A typedef.
    Typedef,
}

impl Ask {
    /// Returns what the editor is headed with.
    #[must_use]
    pub const fn title(self) -> &'static str {
        match self {
            Self::Rename => "Rename",
            Self::Comment => "Comment",
            Self::Question => "Ask a question",
            Self::Type => "Set type",
            Self::Declare => "Declare C",
            Self::Enum => "New enum (Name: A = 1, B)",
            Self::Typedef => "New typedef (Name = type)",
        }
    }

    /// Returns the kind of edit the ask makes of a referent, `None` for one that edits
    /// none: declarations, an enum or a typedef.
    #[must_use]
    pub const fn kind(self) -> Option<Kind> {
        match self {
            Self::Rename => Some(Kind::Rename),
            Self::Comment | Self::Question => Some(Kind::Comment),
            Self::Type => Some(Kind::Retype),
            Self::Declare | Self::Enum | Self::Typedef => None,
        }
    }

    /// Returns the form the ask takes of `r` over `loaded`, or the engine's refusal; an ask
    /// that edits no referent takes its form alone.
    ///
    /// Must be called inside [`crate::worker::spawn_engine`].
    ///
    /// # Arguments
    ///
    /// * `loaded` - The state the edit would be made over.
    /// * `r` - The referent, `None` where there is none.
    ///
    /// # Errors
    ///
    /// The engine's sentence when the referent takes no edit of the kind, or that there is
    /// none for an ask that needs one.
    pub fn offered(self, loaded: &LoadedBinary, r: Option<&Ref>) -> Result<Offer, String> {
        match (self.kind(), r) {
            (Some(kind), Some(r)) => offer_blocking(loaded, r, kind),
            (Some(_) | None, _) => self.alone(),
        }
    }

    /// Returns the form the ask takes with no referent, nothing typed: declarations, an
    /// enum or a typedef.
    ///
    /// # Errors
    ///
    /// For an ask that edits a referent, that there is none.
    pub fn alone(self) -> Result<Offer, String> {
        let form = match self {
            Self::Declare => Form::Declare,
            Self::Enum => Form::Enum,
            Self::Typedef => Form::Alias,
            Self::Rename | Self::Comment | Self::Question | Self::Type => {
                return Err(format!("{}: nothing is under the cursor", self.title()));
            }
        };
        Ok(Offer {
            form,
            now: String::new(),
        })
    }

    /// Returns the text the editor opens with: what the target holds now, as it holds it;
    /// for a question the comment there when it is one, else the `?` it opens with before
    /// the comment there, so asking keeps what was written.
    ///
    /// # Arguments
    ///
    /// * `now` - What the target holds now.
    #[must_use]
    pub fn prefill(self, now: &str) -> String {
        match self {
            Self::Question if open_question(now).is_none() => format!("? {now}"),
            Self::Rename
            | Self::Comment
            | Self::Question
            | Self::Type
            | Self::Declare
            | Self::Enum
            | Self::Typedef => now.to_owned(),
        }
    }
}

/// Tells whether `plan` leaves every entry as it found it, so committing it would change
/// nothing.
///
/// # Arguments
///
/// * `plan` - The plan.
fn changes_nothing(plan: &Plan) -> bool {
    plan.changes().iter().all(Change::changes_nothing)
}

/// What the inline editor tells the view it sits in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Annotated {
    /// It closed, committing or not.
    Closed,
}

/// The engine's answer for the text typed: its number among the answers that landed, the
/// text, and the plan with its lines or the refusal.
type Answer = (u64, String, Result<(Plan, Vec<String>), String>);

/// Rows under the text field, whatever they hold: the hidden characters written out, the
/// plan's lines or its refusal, and the hint; the editor never changes its height.
const SAID_ROWS: usize = 4;

/// How long typing pauses before what is typed is planned.
pub const DEBOUNCE: std::time::Duration = std::time::Duration::from_millis(30);

/// Most rows a declarations editor grows to.
const DECLARE_ROWS: usize = 8;

/// Narrowest the inline editor draws in a code tab, in rems, so its text field has room to
/// type in, unless the tab is narrower; it grows to its longest line and stops at the tab's
/// width.
pub(crate) const INPUT_MIN_REMS: f32 = 28.0;

/// The inline editor: the text typed, the engine's plan of it, and where it lands.
pub struct Annotator {
    /// The window's binary, through which the plan commits.
    binary: Entity<Binary>,
    /// The state the plans are made over.
    loaded: Arc<LoadedBinary>,
    /// What is asked.
    ask: Ask,
    /// The engine's offer the typed text fills: its form and what the target holds.
    offer: Offer,
    /// Where the edit lands when that is not where the person stood, in the engine's terms.
    note: Option<String>,
    /// The text field.
    input: Entity<Editor>,
    /// The newest answer, for the text it was planned of.
    answer: Option<Answer>,
    /// How many answers have landed, which numbers the next.
    landed: u64,
    /// The number of the answer whose plan's lines were last painted.
    painted: Option<u64>,
    /// The pause before planning what was typed; a newer keystroke drops it.
    pause: Option<gpui::Task<()>>,
    /// The running plan; a newer one stops it.
    job: Job,
    /// The text field's edits, and the binary's, after which it plans again.
    _edits: [Subscription; 2],
}

impl EventEmitter<Annotated> for Annotator {}

impl std::fmt::Debug for Annotator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Annotator")
            .field("ask", &self.ask)
            .field("offer", &self.offer)
            .finish_non_exhaustive()
    }
}

impl Annotator {
    /// Returns an inline editor for `ask` filling `offer`'s form over `loaded`, opened with
    /// what the target holds now and planned at once.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary.
    /// * `loaded` - The state the plans are made over.
    /// * `(ask, offer)` - What is asked and the engine's form for it.
    /// * `note` - Where the edit lands, when not where the person stood.
    /// * `window` - Window the editor is in.
    /// * `cx` - Editor context.
    pub fn new(
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        (ask, offer): (Ask, Offer),
        note: Option<String>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let text = ask.prefill(&offer.now);
        let font = ThemeSettings::get_global(cx).buffer_font.clone();
        let input = cx.new(|cx| {
            let mut input = if ask == Ask::Declare {
                Editor::auto_height(1, DECLARE_ROWS, window, cx)
            } else {
                Editor::single_line(window, cx)
            };
            input.set_text(text.clone(), window, cx);
            input.set_placeholder_text(ask.title(), window, cx);
            input.set_text_style_refinement(TextStyleRefinement {
                font_family: Some(font.family),
                font_features: Some(font.features),
                ..TextStyleRefinement::default()
            });
            input
        });
        let edits = cx.subscribe(&input, |this, _, event: &EditorEvent, cx| {
            if matches!(event, EditorEvent::BufferEdited) {
                this.pause(cx);
            }
        });
        let revised = cx.subscribe(&binary, |this, _, event: &BinaryEvent, cx| match event {
            BinaryEvent::Revised(loaded) => {
                this.loaded = loaded.clone();
                this.plan(cx);
            }
            BinaryEvent::Opened(_) | BinaryEvent::Closed => this.cancel(cx),
            BinaryEvent::Rechecked { .. } => {}
        });
        let mut this = Self {
            binary,
            loaded,
            ask,
            offer,
            note,
            input,
            answer: None,
            landed: 0,
            painted: None,
            pause: None,
            job: Job::default(),
            _edits: [edits, revised],
        };
        this.plan(cx);
        this
    }

    /// Returns the text field.
    #[must_use]
    pub const fn input(&self) -> &Entity<Editor> {
        &self.input
    }

    /// Returns the engine's lines for the text typed now, or its refusal; `None` while the
    /// plan runs.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the text field.
    #[must_use]
    pub fn said(&self, cx: &gpui::App) -> Option<Result<Vec<String>, String>> {
        let text = self.input.read(cx).text(cx);
        let (_, planned, answer) = self.answer.as_ref()?;
        (*planned == text).then(|| {
            answer
                .as_ref()
                .map(|(_, said)| said.clone())
                .map_err(Clone::clone)
        })
    }

    /// Plans what was typed once typing pauses for [`DEBOUNCE`]; a newer keystroke drops the
    /// pause before.
    ///
    /// # Arguments
    ///
    /// * `cx` - Editor context.
    fn pause(&mut self, cx: &mut Context<'_, Self>) {
        self.job.stop();
        self.pause = Some(cx.spawn(async move |this, cx| {
            cx.background_executor().timer(DEBOUNCE).await;
            this.update(cx, |this, cx| this.plan(cx)).unwrap_or(());
        }));
    }

    /// Plans the text typed in the background; a newer text stops the plan before.
    ///
    /// # Arguments
    ///
    /// * `cx` - Editor context.
    fn plan(&mut self, cx: &mut Context<'_, Self>) {
        self.pause = None;
        let text = self.input.read(cx).text(cx);
        let (loaded, offer, typed) = (self.loaded.clone(), self.offer.clone(), text.clone());
        let work = move || plan_form_blocking(&loaded, &offer.form, &typed);
        self.job.run(
            format!("Planning: {}", self.ask.title()),
            cx,
            work,
            move |this, planned, cx| {
                this.landed = this.landed.saturating_add(1);
                this.answer = Some((this.landed, text, planned));
                cx.notify();
            },
        );
    }

    /// Returns how many rows the editor takes, the same while it is open: its heading, the
    /// text field, the note, [`SAID_ROWS`], and one for its frame.
    #[must_use]
    pub fn rows(&self) -> u32 {
        let field = if self.ask == Ask::Declare {
            DECLARE_ROWS
        } else {
            1
        };
        let rows = field
            .saturating_add(usize::from(self.note.is_some()))
            .saturating_add(SAID_ROWS)
            .saturating_add(2);
        u32::try_from(rows).unwrap_or(u32::MAX)
    }

    /// Commits the plan whose lines are on screen for the text typed now, through the
    /// binary's edit path, and closes once it lands; a refusal on screen, or a plan not yet
    /// shown for this text, commits nothing, and a commit the binary refuses keeps the
    /// editor and its text, planned again over the state now.
    ///
    /// # Arguments
    ///
    /// * `cx` - Editor context.
    pub fn confirm(&mut self, cx: &mut Context<'_, Self>) {
        let text = self.input.read(cx).text(cx);
        let Some((id, planned, Ok((plan, _)))) = &self.answer else {
            return;
        };
        if *planned != text {
            return;
        }
        if changes_nothing(plan) {
            self.cancel(cx);
            return;
        }
        if self.painted != Some(*id) {
            return;
        }
        let shown = Shown::new(plan.clone());
        let heard = self
            .binary
            .update(cx, |binary, cx| binary.commit(shown, Author::Person, cx));
        cx.spawn(async move |this, cx| {
            let landed = matches!(heard.await, Ok(Committed::Done));
            this.update(cx, |this, cx| {
                if landed {
                    cx.emit(Annotated::Closed);
                } else {
                    this.plan(cx);
                }
            })
            .unwrap_or(());
        })
        .detach();
    }

    /// Closes the editor, writing nothing.
    ///
    /// # Arguments
    ///
    /// * `cx` - Editor context.
    pub fn cancel(&mut self, cx: &mut Context<'_, Self>) {
        self.job.stop();
        cx.emit(Annotated::Closed);
    }
}

/// An inline editor a view with no text of its own shows in a strip under its rows, and the
/// request that opens it.
#[derive(Debug, Default)]
pub struct Strip {
    /// The editor open, and its events.
    open: Option<(Entity<Annotator>, Subscription)>,
    /// The request for what the referent takes, before the editor opens.
    job: Job,
}

impl Strip {
    /// Returns the strip's element while an editor is open.
    #[must_use]
    pub fn element(&self) -> Option<gpui::AnyElement> {
        let (annotator, _) = self.open.as_ref()?;
        Some(div().p_1().child(annotator.clone()).into_any_element())
    }

    /// Returns the address a referent a row or a byte stands for is at, `None` for one at
    /// no address of its own: a field, a variable, a type.
    ///
    /// # Arguments
    ///
    /// * `r` - The referent.
    #[must_use]
    pub const fn va(r: &Ref) -> Option<u64> {
        match r {
            Ref::Address(va)
            | Ref::Function(va)
            | Ref::Import(va)
            | Ref::Global(va)
            | Ref::String(va)
            | Ref::Comment(va) => Some(*va),
            Ref::Field { .. } | Ref::Variable { .. } | Ref::Type(_) => None,
        }
    }

    /// Asks the engine what `r` takes for `ask` over the binary's state now, then opens the
    /// inline editor in the strip `field` reaches in `view`, over the state then; a refusal
    /// is the status line's, in the engine's words. Closing it gives the focus back to
    /// `back`.
    ///
    /// # Arguments
    ///
    /// * `view` - The view the strip is in.
    /// * `field` - Reaches the strip in the view.
    /// * `binary` - The window's binary.
    /// * `(ask, r, note)` - What is asked, of which referent, and the line naming it.
    /// * `back` - What takes the focus once the editor closes.
    /// * `window` - Window the view is in.
    /// * `cx` - View context.
    pub fn ask<V: 'static>(
        view: &mut V,
        field: fn(&mut V) -> &mut Self,
        binary: Entity<Binary>,
        (ask, r, note): (Ask, Ref, Option<String>),
        back: FocusHandle,
        window: &mut Window,
        cx: &mut Context<'_, V>,
    ) {
        let Some(asked) = binary.read(cx).loaded().cloned() else {
            return;
        };
        let work = move || ask.offered(&asked, Some(&r));
        let label = format!("Asking what takes {}", ask.title());
        field(view)
            .job
            .run_in(label, window, cx, work, move |view, offered, window, cx| {
                let offer = match offered {
                    Ok(offer) => offer,
                    Err(why) => {
                        let why = text::visible(&why).into_owned();
                        binary.update(cx, |binary, cx| binary.set_status(why, cx));
                        return;
                    }
                };
                let Some(loaded) = binary.read(cx).loaded().cloned() else {
                    return;
                };
                let annotator =
                    cx.new(|cx| Annotator::new(binary, loaded, (ask, offer), note, window, cx));
                let events =
                    cx.subscribe_in(&annotator, window, move |view, _, event, window, cx| {
                        if *event == Annotated::Closed {
                            field(view).open = None;
                            window.focus(&back, cx);
                            cx.notify();
                        }
                    });
                window.focus(&annotator.focus_handle(cx), cx);
                field(view).open = Some((annotator, events));
                cx.notify();
            });
    }
}

/// Returns `element` answering Rename, Comment, Ask a Question and Set Type by handing the
/// ask to `ask` on its view.
///
/// # Arguments
///
/// * `element` - The view's root element.
/// * `cx` - View context.
/// * `ask` - Opens the inline editor for an ask in the view.
pub fn answer_asks<E: InteractiveElement, V: 'static>(
    element: E,
    cx: &mut Context<'_, V>,
    ask: fn(&mut V, Ask, &mut Window, &mut Context<'_, V>),
) -> E {
    element
        .on_action(cx.listener(move |v, _: &Rename, w, cx| ask(v, Ask::Rename, w, cx)))
        .on_action(cx.listener(move |v, _: &Comment, w, cx| ask(v, Ask::Comment, w, cx)))
        .on_action(cx.listener(move |v, _: &AskQuestion, w, cx| ask(v, Ask::Question, w, cx)))
        .on_action(cx.listener(move |v, _: &SetType, w, cx| ask(v, Ask::Type, w, cx)))
}

/// Opens the inline editor for `ask` in the active code tab, or says there is none.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary, whose status line says when no code tab is active.
/// * `ask` - What is asked.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
fn in_code_tab(
    workspace: &Workspace,
    binary: &Entity<Binary>,
    ask: Ask,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    match workspace.active_item_as::<DecompileItem>(cx) {
        Some(item) => item.update(cx, |item, cx| item.annotate(ask, window, cx)),
        None => binary.update(cx, |binary, cx| {
            let why = format!("{} opens in a code tab: open a function first", ask.title());
            binary.set_status(why, cx);
        }),
    }
}

/// Registers the annotating actions on `workspace`: each opens the inline editor in the
/// active code tab, a table answering those of its rows first; undo and redo step the
/// binary's history.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    /// Registers `A` to open the inline editor for `ask`.
    fn asks<A: gpui::Action>(workspace: &mut Workspace, binary: &Entity<Binary>, ask: Ask) {
        let to = binary.clone();
        commands::register(workspace, binary, move |workspace, _: &A, window, cx| {
            in_code_tab(workspace, &to, ask, window, cx);
        });
    }
    asks::<Rename>(workspace, binary, Ask::Rename);
    asks::<Comment>(workspace, binary, Ask::Comment);
    asks::<AskQuestion>(workspace, binary, Ask::Question);
    asks::<SetType>(workspace, binary, Ask::Type);
    asks::<DeclareC>(workspace, binary, Ask::Declare);
    asks::<NewEnum>(workspace, binary, Ask::Enum);
    asks::<NewTypedef>(workspace, binary, Ask::Typedef);
    let to = binary.clone();
    commands::register(workspace, binary, move |_, _: &UndoEdit, _, cx| {
        to.update(cx, |binary, cx| binary.step(Way::Undo, cx));
    });
    let to = binary.clone();
    commands::register(workspace, binary, move |_, _: &RedoEdit, _, cx| {
        to.update(cx, |binary, cx| binary.step(Way::Redo, cx));
    });
    let to = binary.clone();
    commands::register(
        workspace,
        binary,
        move |workspace, _: &DeclareHeader, window, cx| {
            declare_header(workspace, &to, window, cx);
        },
    );
}

/// Asks for a header file in the system dialog, reads it through the checked reader in
/// the background, and opens Declare C over its text in the active code tab.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary, which asks for the file.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
fn declare_header(
    workspace: &Workspace,
    binary: &Entity<Binary>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    let Some(item) = workspace.active_item_as::<DecompileItem>(cx) else {
        in_code_tab(workspace, binary, Ask::Declare, window, cx);
        return;
    };
    let tab = item.downgrade();
    let handle = window.window_handle();
    binary.update(cx, |binary, cx| {
        binary.pick(
            ONE_FILE,
            move |_, mut paths, cx| {
                let Some(path) = paths.pop() else {
                    return;
                };
                let read =
                    spawn_engine("Reading a header", cx, move || read_header_blocking(&path));
                cx.spawn(async move |binary, cx| {
                    let opened = match read.await {
                        Some(Ok(text)) => handle.update(cx, |_, window, cx| {
                            let offer = Offer {
                                form: Form::Declare,
                                now: text,
                            };
                            tab.update(cx, |item, cx| {
                                item.open_inline((Ask::Declare, offer), None, window, cx);
                            })
                        }),
                        Some(Err(why)) => Err(why),
                        None => return,
                    };
                    let Err(why) = opened.and_then(|shown| shown) else {
                        return;
                    };
                    if let Some(binary) = binary.upgrade() {
                        binary.update(cx, |binary, cx| binary.set_status(format!("{why:#}"), cx));
                    }
                })
                .detach();
            },
            cx,
        );
    });
}

impl Focusable for Annotator {
    fn focus_handle(&self, cx: &gpui::App) -> FocusHandle {
        self.input.focus_handle(cx)
    }
}

impl Render for Annotator {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let text = self.input.read(cx).text(cx);
        let small = |line: &str, color: Color| {
            Label::new(text::visible(line).into_owned())
                .size(LabelSize::Small)
                .color(color)
                .truncate()
                .into_any_element()
        };
        let mut lines = Vec::new();
        if let Some(note) = &self.note {
            lines.push(small(note, Color::Muted));
        }
        let hidden = matches!(text::visible(&text), std::borrow::Cow::Owned(_));
        if hidden {
            lines.push(small(&format!("written out: {text}"), Color::Muted));
        }
        let room = SAID_ROWS.saturating_sub(usize::from(hidden) + 1);
        match &self.answer {
            Some((_, planned, Ok((plan, _)))) if *planned == text && changes_nothing(plan) => {
                lines.push(small("unchanged; Enter or Escape closes", Color::Muted));
                self.painted = None;
            }
            Some((id, planned, Ok((_, said)))) if *planned == text => {
                let shown = if said.len() > room {
                    room.saturating_sub(1)
                } else {
                    said.len()
                };
                lines.extend(said.iter().take(shown).map(|l| small(l, Color::Default)));
                if said.len() > shown {
                    let more = said.len() - shown;
                    lines.push(small(&format!("and {more} more"), Color::Muted));
                }
                lines.push(small("Enter commits, Escape drops", Color::Muted));
                self.painted = Some(*id);
            }
            Some((_, planned, Err(why))) if *planned == text => {
                let color = if text.trim().is_empty() {
                    Color::Muted
                } else {
                    Color::Error
                };
                lines.push(small(why, color));
                self.painted = None;
            }
            Some(_) | None => {
                lines.push(small("planning...", Color::Muted));
                self.painted = None;
            }
        }
        let colors = cx.theme().colors();
        v_flex()
            .key_context("Annotating")
            .on_action(cx.listener(|this, _: &menu::Confirm, _, cx| this.confirm(cx)))
            .on_action(cx.listener(|this, _: &menu::Cancel, _, cx| this.cancel(cx)))
            .max_w_full()
            .overflow_hidden()
            .font(ThemeSettings::get_global(cx).ui_font.clone())
            .px_2()
            .py_1()
            .gap_0p5()
            .border_1()
            .rounded_sm()
            .border_color(colors.border)
            .bg(colors.editor_background)
            .child(small(self.ask.title(), Color::Muted))
            .child(div().w_full().child(self.input.clone()))
            .children(lines)
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests;
