//! The chat panel: a conversation with a model the person picks, over the open binary, in a
//! Zed dock.
//!
//! The panel is borer's own, built from Zed's `ui` components; the models are Zed's
//! providers ([`providers`]); the agent loop and its tools are the [`thread`]'s. It reads
//! as a document: a header with the model picker, the thread top to bottom, the bars that
//! wait on the person, and the input ([`view`]). Replies are drawn as plain text and code,
//! so nothing in a model's output loads from anywhere.

pub mod card;
mod picker;
pub mod providers;
pub mod thread;
pub mod tools;
mod view;

use std::collections::{BTreeMap, BTreeSet};

use gpui::{
    App, AppContext as _, Context, Entity, EventEmitter, FocusHandle, Focusable, FollowMode,
    InteractiveElement as _, IntoElement, ListAlignment, ListState, ParentElement as _, Render,
    SharedString, Styled as _, Subscription, Task, WeakEntity, Window, list, px,
};
use ui::{IconName, PopoverMenuHandle, v_flex};
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel, PanelEvent};

use borer_engine::text;

use crate::app_assets::Glyph;
use crate::binary::Binary;
use crate::decompile_item::TabMode;
use crate::panels::{PanelSpec, remove, spec_panel};
use crate::places::{self, Opening};
use crate::rows_panel::Empty;
use crate::worker::{place_at, spawn_engine};
#[cfg(test)]
pub(crate) use card::lines as card_lines;
pub use picker::ChatPicker;
use providers::{Endpoint, Offered};
use thread::{Chosen, Entry, Thread};

gpui::actions!(
    borer,
    [
        /// Shows the chat panel and focuses it, or moves focus back to the center pane.
        ToggleChat,
        /// Stops the chat's running turn: its stream and its tool calls are dropped.
        StopChat,
        /// Starts a new chat thread: the running turn stops and the conversation is forgotten.
        NewChatThread,
        /// Sends what the chat's input holds to the chosen model.
        SendChat,
        /// Keeps the key typed in the chat's key field in the system keychain.
        SaveChatKey,
        /// Picks the chat's next provider and asks it for its models.
        NextChatProvider,
        /// Makes the picked provider's next model the one the chat sends to.
        NextChatModel,
        /// Accepts the chat's proposal whose card has focus: its plan commits through the
        /// edit path with the model as author.
        AcceptChatProposal,
        /// Rejects the chat's proposal whose card has focus; nothing is written.
        RejectChatProposal,
        /// Sends the chat message held for your agreement, to the receiver its notice named.
        SendHeldChat,
        /// Drops the chat message held for your agreement; nothing is sent.
        DontSendHeldChat,
        /// Plans the chat's stale proposal again over the names as they are now.
        PlanChatProposalAgain,
        /// Opens the chat's model picker: providers, models and the key field.
        PickChatModel,
        /// Sends again the message of the chat's newest turn a provider failed.
        RetryChat,
        /// Opens or closes the chat's newest tool call.
        ToggleChatCall,
        /// Opens the function at the address the chat's newest tool call read.
        OpenChatCallAddress,
        /// Asks to forget the picked chat provider's saved key; the picker confirms it.
        ForgetChatKey,
    ]
);

/// How far past the visible entries the conversation's list draws, in pixels.
const LIST_OVERDRAW: f32 = 200.0;

/// Most lines the input grows to before it scrolls.
const INPUT_LINES: usize = 6;

/// A card's entry, its verdict's kind and whether it is the head: what decides its height.
type CardState = (usize, std::mem::Discriminant<thread::Verdict>, bool);

/// The chat panel's row of [`crate::panels::PANELS`].
pub const PANEL: PanelSpec = PanelSpec {
    key: "Chat",
    title: "Chat",
    icon: Glyph::Zed(IconName::Chat),
    toggle: &ToggleChat,
    dock: DockPosition::Right,
    docks: &[
        DockPosition::Right,
        DockPosition::Left,
        DockPosition::Bottom,
    ],
    size_px: 380.0,
    hooks: crate::rail::panel::<ChatPanel>(),
    add: |workspace, binary, dock, window, cx| {
        let at = workspace.weak_handle();
        let panel = cx.new(|cx| ChatPanel::new(binary, (at, dock), window, cx));
        workspace.add_panel(panel, window, cx);
    },
    remove: remove::<ChatPanel>,
    focus: |workspace, window, cx| {
        (crate::rail::panel::<ChatPanel>().click)(workspace, window, cx);
    },
    current: always_current,
};

/// Returns true: the chat row's [`PanelSpec::current`]. The chat draws no view of the
/// binary's state; its thread forgets itself when the binary changes.
const fn always_current(_: &Workspace, _: Option<u64>, _: &App) -> bool {
    true
}

/// Registers the chat's window-wide commands on `workspace`: Stop, New Thread, Send, Save
/// Key, picking the next provider or model, Send or Don't Send a held message, and Plan
/// Again.
///
/// They are in reach as their rows say, whatever has focus. Accept and Reject act only on the
/// card of the oldest proposal that waits while it has focus ([`ChatPanel::card`]); from
/// anywhere else they scroll to that card, move focus to it and decide nothing.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    crate::commands::register_boxed(workspace, binary, &StopChat, |workspace, _, cx| {
        on_thread(workspace, cx, Thread::stop);
    });
    crate::commands::register_boxed(workspace, binary, &NewChatThread, |workspace, _, cx| {
        on_thread(workspace, cx, Thread::clear);
    });
    let verdicts: [&'static dyn gpui::Action; 2] = [&AcceptChatProposal, &RejectChatProposal];
    for verdict in verdicts {
        crate::commands::register_boxed(workspace, binary, verdict, |workspace, window, cx| {
            on_panel(workspace, window, cx, ChatPanel::show_head);
        });
    }
    crate::commands::register_boxed(workspace, binary, &SendHeldChat, |workspace, _, cx| {
        on_thread(workspace, cx, |thread, cx| {
            if thread.held().is_some() {
                thread.agree(cx);
            }
        });
    });
    crate::commands::register_boxed(workspace, binary, &PickChatModel, |workspace, w, cx| {
        on_panel(workspace, w, cx, |panel, window, cx| {
            panel.picker.show(window, cx);
        });
    });
    crate::commands::register_boxed(workspace, binary, &ForgetChatKey, |workspace, w, cx| {
        on_panel(workspace, w, cx, ChatPanel::ask_to_forget);
    });
    crate::commands::register_boxed(workspace, binary, &RetryChat, |workspace, w, cx| {
        on_panel(workspace, w, cx, |panel, _, cx| {
            let failed = panel.thread.read(cx).entries().len().checked_sub(1);
            if let Some(ix) = failed {
                panel.retry(ix, cx);
            }
        });
    });
    crate::commands::register_boxed(workspace, binary, &ToggleChatCall, |workspace, w, cx| {
        on_panel(workspace, w, cx, |panel, _, cx| {
            if let Some(ix) = panel.newest_call(cx) {
                panel.toggle_call(ix, cx);
            }
        });
    });
    crate::commands::register_boxed(workspace, binary, &OpenChatCallAddress, |w, win, cx| {
        on_panel(w, win, cx, |panel, window, cx| {
            let thread = panel.thread.read(cx);
            let at = panel
                .newest_call(cx)
                .and_then(|ix| thread.call_at(ix)?.key.clone());
            let va = at
                .filter(|k| k.1 == thread::Arg::Address)
                .and_then(|k| u64::from_str_radix(k.0.strip_prefix("0x")?, 16).ok());
            if let Some(va) = va {
                panel.open_address(va, window, cx);
            }
        });
    });
    crate::commands::register_boxed(workspace, binary, &DontSendHeldChat, |workspace, _, cx| {
        on_thread(workspace, cx, Thread::decline);
    });
    crate::commands::register_boxed(workspace, binary, &PlanChatProposalAgain, |w, _, cx| {
        on_thread(w, cx, |thread, cx| {
            if let Some(id) = thread.head() {
                thread.plan_again(id, cx);
            }
        });
    });
    crate::commands::register_boxed(workspace, binary, &SendChat, |workspace, window, cx| {
        on_panel(workspace, window, cx, ChatPanel::send);
    });
    crate::commands::register_boxed(workspace, binary, &SaveChatKey, |workspace, window, cx| {
        on_panel(workspace, window, cx, ChatPanel::save_key);
    });
    crate::commands::register_boxed(workspace, binary, &NextChatProvider, |workspace, w, cx| {
        on_panel(workspace, w, cx, ChatPanel::next_provider);
    });
    crate::commands::register_boxed(workspace, binary, &NextChatModel, |workspace, w, cx| {
        on_panel(workspace, w, cx, |panel, _, cx| panel.next_model(cx));
    });
}

/// Runs `act` on the chat panel, when it is docked.
fn on_panel(
    workspace: &Workspace,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
    act: impl FnOnce(&mut ChatPanel, &mut Window, &mut Context<'_, ChatPanel>),
) {
    if let Some(panel) = workspace.panel::<ChatPanel>(cx) {
        panel.update(cx, |panel, cx| act(panel, window, cx));
    }
}

/// Runs `act` on the chat panel's thread, when the panel is docked.
fn on_thread(
    workspace: &Workspace,
    cx: &mut Context<'_, Workspace>,
    act: impl FnOnce(&mut Thread, &mut Context<'_, Thread>),
) {
    if let Some(panel) = workspace.panel::<ChatPanel>(cx) {
        let thread = panel.read(cx).thread.clone();
        thread.update(cx, act);
    }
}

/// The chat panel.
pub struct ChatPanel {
    /// The window's binary, whose absence the panel's card says.
    binary: Entity<Binary>,
    /// The conversation.
    thread: Entity<Thread>,
    /// The workspace the panel is docked in, where an address opens its function.
    workspace: WeakEntity<Workspace>,
    /// Where the person writes, growing to a few lines; Enter sends, Shift+Enter breaks a
    /// line.
    input: Entity<editor::Editor>,
    /// The conversation as a list that draws only the entries in view and follows the
    /// newest unless the person scrolled up.
    list: ListState,
    /// The entries of the tool calls the person opened, by index.
    opened: BTreeSet<usize>,
    /// The code blocks' color runs of each finished message, by entry, read once.
    colors: BTreeMap<usize, view::Colors>,
    /// The streaming reply's entry and the color runs of its closed code blocks, read once
    /// each as its fence closes; only its open block is read while it draws.
    streamed: Option<(usize, view::Colors)>,
    /// Each card's state as last measured: a card whose state moved is measured again.
    cards: Vec<CardState>,
    /// Opens and closes the model picker's popover.
    picker: PopoverMenuHandle<ChatPicker>,
    /// The proposal whose card took Enter's key down; its key up accepts it, so a key
    /// held down or pressed elsewhere decides nothing.
    armed: Option<usize>,
    /// Whether the picker asks to confirm forgetting the picked provider's saved key.
    forgetting: bool,
    /// Whether the input holds a message that can be sent ([`view::sendable`]), kept as the
    /// input is edited so the Send button reads it without reading the input each frame.
    sendable: bool,
    /// What the last action that changed nothing found, as an address in no function.
    note: Option<SharedString>,
    /// Where the person types the picked provider's API key.
    key: Entity<editor::Editor>,
    /// The provider the person picked.
    picked: Option<Offered>,
    /// The picked provider's models, once it listed them.
    models: Vec<Chosen>,
    /// Lists the picked provider's models or saves its key; dropping it stops that.
    listing: Task<()>,
    /// Why the last pick or key save failed.
    error: Option<SharedString>,
    /// Focus handle of the panel's root.
    focus_handle: FocusHandle,
    /// Whether the panel is shown in its dock; a hidden panel sends nothing.
    shown: bool,
    /// Focus handle of the card of the oldest proposal that waits, where Accept and Reject
    /// are in reach.
    card: FocusHandle,
    /// Dock the panel sits in.
    position: DockPosition,
    /// Redraws on the thread's and the registry's changes.
    _subscriptions: Vec<Subscription>,
}

impl std::fmt::Debug for ChatPanel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ChatPanel")
            .field("picked", &self.picked)
            .finish_non_exhaustive()
    }
}

impl ChatPanel {
    /// Returns a panel over `binary` with an empty thread and no provider picked.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary.
    /// * `(workspace, position)` - The workspace the panel is docked in, and the dock it
    ///   starts in.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    #[must_use]
    pub fn new(
        binary: &Entity<Binary>,
        (workspace, position): (WeakEntity<Workspace>, DockPosition),
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let thread = cx.new(|cx| Thread::new(binary, cx));
        let input = cx.new(|cx| {
            let mut editor = editor::Editor::auto_height(1, INPUT_LINES, window, cx);
            editor.set_placeholder_text("Ask about this binary", window, cx);
            editor
        });
        let key = Self::key_field(window, cx);
        let list = ListState::new(0, ListAlignment::Top, px(LIST_OVERDRAW));
        list.set_follow_mode(FollowMode::Tail);
        Self {
            _subscriptions: vec![
                cx.observe(&thread, |this, _, cx| this.follow(cx)),
                cx.observe(binary, |_, _, cx| cx.notify()),
                cx.subscribe(&input, |this, input, event: &editor::EditorEvent, cx| {
                    if matches!(event, editor::EditorEvent::BufferEdited) {
                        this.sendable = view::sendable(&input.read(cx).text(cx));
                        cx.notify();
                    }
                }),
            ],
            binary: binary.clone(),
            thread,
            workspace,
            input,
            list,
            opened: BTreeSet::new(),
            colors: BTreeMap::new(),
            streamed: None,
            cards: Vec::new(),
            picker: PopoverMenuHandle::default(),
            armed: None,
            forgetting: false,
            sendable: false,
            note: None,
            key,
            picked: None,
            models: Vec::new(),
            listing: Task::ready(()),
            error: None,
            focus_handle: cx.focus_handle(),
            shown: false,
            card: cx.focus_handle(),
            position,
        }
    }

    /// Returns whether a turn is running, whether the panel is shown or hidden: hiding it
    /// does not stop one, so the status bar can mark the chat while a turn runs hidden.
    ///
    /// # Arguments
    ///
    /// * `cx` - App context.
    #[must_use]
    pub fn is_running(&self, cx: &App) -> bool {
        self.thread.read(cx).is_running()
    }

    /// Returns the conversation.
    #[must_use]
    pub const fn thread(&self) -> &Entity<Thread> {
        &self.thread
    }

    /// Keeps the list in step with the thread: new entries join it and the newest, which a
    /// streaming reply grows, is measured again, as are the cards whose state changed and
    /// the opened tool calls; a cleared thread starts it over, and a message the person
    /// sends follows the newest entry again after a reveal stopped it.
    fn follow(&mut self, cx: &mut Context<'_, Self>) {
        let thread = self.thread.read(cx);
        let (old, new) = (self.list.item_count(), thread.entries().len());
        let head = thread.head();
        let cards: Vec<CardState> = thread
            .entries()
            .iter()
            .enumerate()
            .filter_map(|(ix, e)| match e {
                Entry::Proposal(id) => {
                    let p = thread.proposal(*id)?;
                    Some((ix, std::mem::discriminant(&p.verdict), head == Some(*id)))
                }
                Entry::Person(_)
                | Entry::Model(_)
                | Entry::Tool(_)
                | Entry::Notice(_)
                | Entry::Error(_) => None,
            })
            .collect();
        if new < old {
            self.list.reset(new);
            self.opened.clear();
            self.colors.clear();
            self.streamed = None;
        } else {
            let from = old.saturating_sub(1);
            self.list.splice(from..old, new - from);
            let wrote = thread
                .entries()
                .get(old..)
                .unwrap_or_default()
                .iter()
                .any(|e| matches!(e, Entry::Person(_)));
            if wrote {
                self.list.set_follow_mode(FollowMode::Tail);
            }
            let moved = cards.iter().filter(|c| !self.cards.contains(c));
            for ix in moved.map(|c| c.0).chain(self.opened.iter().copied()) {
                if ix < from {
                    self.list.splice(ix..ix.saturating_add(1), 1);
                }
            }
        }
        let streaming = thread.is_running().then(|| new.saturating_sub(1));
        for (ix, entry) in thread.entries().iter().enumerate() {
            let (Entry::Model(said) | Entry::Person(said)) = entry else {
                continue;
            };
            if streaming != Some(ix) {
                self.colors
                    .entry(ix)
                    .or_insert_with(|| view::text_colors(&text::visible(said)));
                continue;
            }
            let said = text::visible(said);
            let closed = view::closed_code_blocks(&said);
            if self
                .streamed
                .as_ref()
                .is_none_or(|(at, kept)| *at != ix || kept.len() < closed)
            {
                let mut kept = view::text_colors(&said);
                kept.truncate(closed);
                self.streamed = Some((ix, kept));
            }
        }
        self.cards = cards;
        cx.notify();
    }

    /// Shows `models` as `offer`'s list without asking the provider, as the chat demo does:
    /// nothing is sent anywhere.
    pub(crate) fn offer_listed(
        &mut self,
        offer: Offered,
        models: Vec<Chosen>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.key = Self::key_field(window, cx);
        self.picked = Some(offer);
        self.models = models;
        cx.notify();
    }

    /// Returns the handle that opens and closes the model picker.
    pub(crate) const fn picker(&self) -> &PopoverMenuHandle<ChatPicker> {
        &self.picker
    }

    /// Sends again what the error at entry `ix` failed on, when it is the newest failed turn
    /// and none runs ([`Thread::retry_at`]); nothing otherwise.
    fn retry(&self, ix: usize, cx: &mut Context<'_, Self>) {
        self.thread.update(cx, |t, cx| {
            if let Some(said) = t.retry_at(ix).map(str::to_owned) {
                t.send(said, cx);
            }
        });
    }

    /// Returns the entry of the newest tool call, if any.
    fn newest_call(&self, cx: &App) -> Option<usize> {
        let thread = self.thread.read(cx);
        (0..thread.entries().len())
            .rev()
            .find(|ix| thread.call_at(*ix).is_some())
    }

    /// Opens or closes the tool call at entry `ix`.
    pub(crate) fn toggle_call(&mut self, ix: usize, cx: &mut Context<'_, Self>) {
        if !self.opened.remove(&ix) {
            self.opened.insert(ix);
        }
        self.list.splice(ix..ix.saturating_add(1), 1);
        cx.notify();
    }

    /// Scrolls to the card of the oldest proposal that waits and gives it focus, where
    /// Enter accepts and Escape rejects.
    pub(crate) fn show_head(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let thread = self.thread.read(cx);
        let Some(id) = thread.head() else {
            return;
        };
        let at = thread
            .entries()
            .iter()
            .position(|e| *e == Entry::Proposal(id));
        if let Some(ix) = at {
            self.list.pause_following_tail();
            self.list.scroll_to_reveal_item(ix);
        }
        self.card.focus(window, cx);
        cx.notify();
    }

    /// Opens what is at `va` as a Ctrl+click on a call does: the function it starts in a
    /// preview tab, or the listing at it inside its function; nothing when no function
    /// holds it. The function is found in the background.
    fn open_address(&mut self, va: u64, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.note = None;
        let Some(loaded) = self.binary.read(cx).loaded().cloned() else {
            return;
        };
        let (workspace, binary) = (self.workspace.clone(), self.binary.clone());
        let held = loaded.clone();
        let found = spawn_engine(format!("Chat: open {va:#x}"), cx, move || {
            place_at(&held, va)
        });
        cx.spawn_in(window, async move |this, cx| {
            let Some(Some(place)) = found.await else {
                this.update(cx, |this, cx| {
                    this.note = Some(format!("{va:#x} is in no function; nothing opened").into());
                    cx.notify();
                })
                .unwrap_or(());
                return;
            };
            let how = Opening {
                mode: TabMode::Preview,
                focus: true,
            };
            workspace
                .update_in(cx, |workspace, window, cx| {
                    places::open(workspace, &binary, &loaded, place, how, window, cx);
                })
                .unwrap_or(());
        })
        .detach();
    }

    /// Picks `offer` as [`Self::pick`] does; picking another provider than the one picked
    /// empties the key field, so a key is only ever saved for the provider it was typed for.
    fn switch(&mut self, offer: Offered, window: &mut Window, cx: &mut Context<'_, Self>) {
        if self.picked != Some(offer) {
            self.key = Self::key_field(window, cx);
        }
        self.pick(offer, cx);
    }

    /// Picks the provider after the picked one, in the picker's order; the first when none is.
    fn next_provider(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let at = self
            .picked
            .and_then(|picked| Offered::ALL.iter().position(|o| *o == picked))
            .map_or(0, |at| (at + 1) % Offered::ALL.len());
        if let Some(offer) = Offered::ALL.get(at) {
            self.switch(*offer, window, cx);
        }
    }

    /// Makes the model after the chosen one, in the provider's list, the one sends go to.
    fn next_model(&mut self, cx: &mut Context<'_, Self>) {
        let chosen = self.thread.read(cx).chosen().map(|c| c.model.id.clone());
        let at = chosen
            .and_then(|id| self.models.iter().position(|m| m.model.id == id))
            .map_or(0, |at| at.saturating_add(1));
        let next = self.models.get(at).or_else(|| self.models.first());
        if let Some(id) = next.map(|m| m.model.id.0.clone()) {
            self.choose_model(&id, cx);
        }
    }

    /// Picks `offer` and asks it for its models with its key: nothing is sent to a provider
    /// before the person picks it.
    ///
    /// # Arguments
    ///
    /// * `offer` - The provider picked.
    /// * `cx` - Panel context.
    pub fn pick(&mut self, offer: Offered, cx: &mut Context<'_, Self>) {
        self.picked = Some(offer);
        self.models.clear();
        self.error = None;
        let http = match providers::http(cx) {
            Ok(http) => http,
            Err(err) => {
                self.error = Some(format!("{err:#}").into());
                cx.notify();
                return;
            }
        };
        let endpoint = Endpoint::of(offer, cx);
        self.listing = cx.spawn(async move |this, cx| {
            let listed = providers::models(endpoint, http, cx).await;
            this.update(cx, |this, cx| {
                match listed {
                    Ok(models) => this.models = models,
                    Err(err) => this.error = Some(format!("{err:#}").into()),
                }
                cx.notify();
            })
            .unwrap_or(());
        });
        cx.notify();
    }

    /// Makes the model `id` of the picked provider the one sends go to.
    ///
    /// # Arguments
    ///
    /// * `id` - The model's id at the provider.
    /// * `cx` - Panel context.
    pub fn choose_model(&mut self, id: &str, cx: &mut Context<'_, Self>) {
        if let Some(chosen) = self.models.iter().find(|m| m.model.id.0 == id).cloned() {
            self.thread
                .update(cx, |thread, cx| thread.choose(chosen, cx));
        }
    }

    /// Returns an empty key field that masks what is typed in it.
    fn key_field(window: &mut Window, cx: &mut Context<'_, Self>) -> Entity<editor::Editor> {
        cx.new(|cx| {
            let mut editor = editor::Editor::single_line(window, cx);
            editor.set_placeholder_text("API key, kept in the system keychain", window, cx);
            editor.set_masked(true, cx);
            editor
        })
    }

    /// Keeps the key typed in the key field in the system keychain under the picked
    /// provider's URL, and asks the provider for its models again.
    ///
    /// The field is replaced by an empty one, so the key is in no undo history.
    fn save_key(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let Some(offer) = self.picked else {
            return;
        };
        if offer.key_var().is_none() {
            self.error = Some(format!("{} takes no key; nothing was saved", offer.label()).into());
            cx.notify();
            return;
        }
        let typed = self.key.read(cx).text(cx);
        let Some(key) = Some(typed.trim().to_owned()).filter(|k| !k.is_empty()) else {
            self.error = Some("type a key first; nothing was saved".into());
            cx.notify();
            return;
        };
        self.key = Self::key_field(window, cx);
        self.write_key(offer, Some(key), cx);
    }

    /// Asks before forgetting the picked provider's saved key: the picker shows what would
    /// be deleted and the person confirms there ([`Self::forget_key`]).
    fn ask_to_forget(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        if self.picked.is_some_and(|offer| offer.key_var().is_some()) {
            self.forgetting = true;
            self.picker.show(window, cx);
            cx.notify();
        }
    }

    /// Deletes the picked provider's key from the chat's keychain entry
    /// ([`providers::key_entry`]), once the person confirmed it; no other entry is touched.
    fn forget_key(&mut self, cx: &mut Context<'_, Self>) {
        let Some(offer) = self.picked.filter(|_| self.forgetting) else {
            return;
        };
        self.forgetting = false;
        self.write_key(offer, None, cx);
    }

    /// Writes `key` to the chat's keychain entry for `offer`, or deletes it for `None`, then
    /// asks the provider for its models again.
    fn write_key(&mut self, offer: Offered, key: Option<String>, cx: &mut Context<'_, Self>) {
        let url = offer.url(cx);
        self.listing = cx.spawn(async move |this, cx| {
            let saved = providers::save_key(&url, key.as_deref(), cx).await;
            this.update(cx, |this, cx| match saved {
                Ok(()) => this.pick(offer, cx),
                Err(err) => {
                    this.error = Some(format!("the keychain refused the key: {err:#}").into());
                    cx.notify();
                }
            })
            .unwrap_or(());
        });
    }

    /// Sends what the input holds and empties it.
    fn send(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        if !self.shown {
            self.error = Some("the chat is hidden; open it to send".into());
            cx.notify();
            return;
        }
        let text = self.input.read(cx).text(cx);
        if !view::sendable(&text) {
            return;
        }
        if self.thread.read(cx).chosen().is_none() {
            self.picker.show(window, cx);
            return;
        }
        self.input
            .update(cx, |input, cx| input.set_text("", window, cx));
        self.thread.update(cx, |thread, cx| thread.send(text, cx));
    }
}

/// Returns `text` as one line a person reads whole: every character that hides or reorders
/// text written out ([`text::visible`]), then bounded to a row ([`text::one_line`]).
fn shown(text: &str) -> String {
    text::one_line(&text::visible(text))
}

impl Render for ChatPanel {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let binary = self.binary.read(cx);
        if binary.loaded().is_none() {
            return v_flex()
                .key_context("ChatPanel")
                .track_focus(&self.focus_handle)
                .size_full()
                .child(Empty::of_binary(binary).card().render(cx));
        }
        let file = binary
            .loaded()
            .map(|l| crate::recent::file_name(&l.program.path))
            .unwrap_or_default();
        let body = if self.thread.read(cx).entries().is_empty() {
            self.empty_state(&file, cx).into_any_element()
        } else {
            list(
                self.list.clone(),
                cx.processor(|this, ix: usize, window, cx| this.entry(ix, window, cx)),
            )
            .flex_1()
            .into_any_element()
        };
        v_flex()
            .key_context("ChatPanel")
            .track_focus(&self.focus_handle)
            .size_full()
            .on_action(cx.listener(|this, _: &menu::Confirm, window, cx| this.send(window, cx)))
            .child(self.header(cx))
            .child(body)
            .child(self.bars(cx))
            .child(self.composer(cx))
    }
}

impl EventEmitter<PanelEvent> for ChatPanel {}

impl Focusable for ChatPanel {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Panel for ChatPanel {
    spec_panel!(PANEL);

    fn activation_focus_handle(&self, cx: &App) -> FocusHandle {
        self.input.focus_handle(cx)
    }

    fn set_active(&mut self, active: bool, _window: &mut Window, _cx: &mut Context<'_, Self>) {
        self.shown = active;
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests;
