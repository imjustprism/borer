//! The overview: what the open file is, how it is protected, what it can do and which
//! functions to read first, in the engine's triage words and order, every address a link.

use std::ops::Range;
use std::sync::Arc;

use borer_engine::analysis::render::{Basis, INCOMPLETE_NOTE, Reason, Triage};
use gpui::{
    AnyElement, App, Context, Entity, EventEmitter, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, ScrollStrategy, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, UniformListScrollHandle,
    WeakEntity, Window, div, px, uniform_list,
};
use theme::ActiveTheme as _;
use ui::{Color, Icon, IconName, Label, LabelCommon as _, LabelSize, h_flex};
use workspace::item::ItemEvent;
use workspace::{Item, Workspace};

use crate::actions::Overview;
use crate::binary::{Binary, BinaryEvent, Revision};
use crate::card::{Card, Tone};
use crate::commands;
use crate::decompile_item::TabMode;
use crate::places::{Opening, Place, open};
use crate::worker::{Job, LoadedBinary, place_at, triage_blocking};

/// Logical pixels a line under a heading is indented by.
const INDENT_PX: f32 = 16.0;

/// How a line of the overview reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Look {
    /// A block's name, muted.
    Heading,
    /// A line of the engine's words.
    Plain,
    /// A line about what the engine could not do or see.
    Warning,
    /// A line under the line before it: an address of a section, a reason of a function.
    Under,
}

/// One line of the overview.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    /// The engine's words, or an address it gave.
    pub text: SharedString,
    /// How the line reads.
    pub look: Look,
    /// The address of the triage the line names and the place it opens; `None` for a line
    /// that opens nothing.
    pub link: Option<(u64, Place)>,
    /// How the engine knows a reason, `None` on every line but a reason's.
    pub basis: Option<Basis>,
}

/// Returns the words a reason's basis is labelled with and the theme color they draw in:
/// observed in the theme's `status().success`, static in `status().info`, pattern in
/// `text_muted`.
///
/// # Arguments
///
/// * `basis` - How the engine knows the reason.
#[must_use]
pub const fn basis_label(basis: Basis) -> (&'static str, Color) {
    match basis {
        Basis::Observed => ("observed by running", Color::Success),
        Basis::Static => ("static reference", Color::Info),
        Basis::Pattern => ("pattern match", Color::Muted),
    }
}

/// Returns the address a reason names, `None` for a reason about counts.
///
/// # Arguments
///
/// * `reason` - The reason.
const fn reason_at(reason: &Reason) -> Option<u64> {
    match reason {
        Reason::Builds { written_at, .. } => Some(*written_at),
        Reason::Calls { callee, .. } => Some(*callee),
        Reason::Holds { at, .. } => Some(*at),
        Reason::References { .. } => None,
    }
}

/// Returns the overview's lines of `triage`: the file, each section with its addresses,
/// the blind spots and the functions to read first, in the triage's order.
///
/// A list the engine cut short says `showing N of M` under it.
///
/// # Arguments
///
/// * `triage` - The engine's triage.
/// * `place` - What an address opens, `None` for an address that opens nothing.
#[must_use]
pub fn rows(triage: &Triage, place: impl Fn(u64) -> Option<Place>) -> Vec<Row> {
    let line = |text: &str, look, at: Option<u64>| Row {
        text: SharedString::from(text.to_owned()),
        look,
        link: at.and_then(|at| Some((at, place(at)?))),
        basis: None,
    };
    let mut out = vec![
        line(&triage.name, Look::Heading, None),
        line(&triage.shape, Look::Plain, None),
    ];
    if triage.incomplete {
        out.push(line(
            INCOMPLETE_NOTE.trim_start_matches("# "),
            Look::Warning,
            None,
        ));
    }
    out.extend(
        triage
            .file
            .iter()
            .map(|l| line(l.trim_start_matches("# "), Look::Plain, None)),
    );
    for section in &triage.sections {
        let summary = &section.summary;
        out.push(line(section.kind.label(), Look::Heading, None));
        out.push(line(&summary.headline, Look::Plain, None));
        let at = summary.at.iter();
        out.extend(at.map(|&at| line(&format!("{at:#x}"), Look::Under, Some(at))));
        if summary.at_total > summary.at.len() {
            let shown = format!("showing {} of {}", summary.at.len(), summary.at_total);
            out.push(line(&shown, Look::Under, None));
        }
    }
    if !triage.blind_spots.is_empty() {
        out.push(line("blind spots", Look::Heading, None));
        out.extend(
            triage
                .blind_spots
                .iter()
                .map(|s| line(s, Look::Warning, None)),
        );
    }
    if !triage.read_first.is_empty() {
        out.push(line("read first", Look::Heading, None));
    }
    for function in &triage.read_first {
        let name = format!("{}  score {}", function.name, function.score);
        out.push(line(&name, Look::Plain, Some(function.entry)));
        for reason in &function.reasons {
            let basis = Some(reason.basis());
            out.push(Row {
                basis,
                ..line(&reason.to_string(), Look::Under, reason_at(reason))
            });
        }
    }
    if triage.candidates > triage.read_first.len() {
        let listed = triage.read_first.len();
        let shown = format!("showing {listed} of {}", triage.candidates);
        out.push(line(&shown, Look::Plain, None));
    }
    out
}

/// How the overview opens: a permanent tab, focused.
const SHOWN: Opening = Opening {
    mode: TabMode::Permanent,
    focus: true,
};

/// Opens the overview of each binary the window loads.
///
/// # Arguments
///
/// * `binary` - The window's binary.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn open_on_load(binary: &Entity<Binary>, window: &mut Window, cx: &mut Context<'_, Workspace>) {
    cx.subscribe_in(binary, window, |workspace, binary, event, window, cx| {
        if let BinaryEvent::Opened(loaded) = event {
            open(
                workspace,
                binary,
                loaded,
                Place::Overview,
                SHOWN,
                window,
                cx,
            );
        }
    })
    .detach();
}

/// Registers the overview's command on `workspace`, which opens the overview of the
/// window's `binary` again from anywhere.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let held = binary.clone();
    commands::register(
        workspace,
        binary,
        move |workspace, _: &Overview, window, cx| {
            if let Some(loaded) = held.read(cx).loaded().cloned() {
                open(
                    workspace,
                    &held,
                    &loaded,
                    Place::Overview,
                    SHOWN,
                    window,
                    cx,
                );
            }
        },
    );
}

/// A center tab showing the engine's triage of the open binary.
pub struct OverviewItem {
    /// Workspace the links open in.
    workspace: WeakEntity<Workspace>,
    /// The window's binary.
    binary: Entity<Binary>,
    /// The binary the triage is of.
    loaded: Arc<LoadedBinary>,
    /// The lines, empty until the triage is built.
    rows: Vec<Row>,
    /// The highlighted line, a link, `None` while there is none.
    selected: Option<usize>,
    /// Scroll of the lines.
    scroll: UniformListScrollHandle,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
    /// The background triage.
    job: Job,
    /// Closes the tab once its binary is closed or another load starts, and triages again
    /// the state an edit or a project leaves.
    _follows: Subscription,
}

impl std::fmt::Debug for OverviewItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OverviewItem")
            .field("rows", &self.rows.len())
            .field("job", &self.job)
            .finish_non_exhaustive()
    }
}

impl OverviewItem {
    /// Returns the overview of `loaded`, its triage built in the background, and again over
    /// each state an edit or a project leaves.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the links open in.
    /// * `binary` - The window's binary.
    /// * `loaded` - The binary to triage.
    /// * `cx` - Item context.
    #[must_use]
    pub fn new(
        workspace: WeakEntity<Workspace>,
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let follows = cx.subscribe(&binary, |item, _, event, cx| match event {
            BinaryEvent::Closed => cx.emit(ItemEvent::CloseItem),
            BinaryEvent::Revised(loaded) => item.build(loaded.clone(), cx),
            BinaryEvent::Opened(_) | BinaryEvent::Rechecked { .. } => {}
        });
        let mut item = Self {
            workspace,
            binary,
            loaded: loaded.clone(),
            rows: Vec::new(),
            selected: None,
            scroll: UniformListScrollHandle::new(),
            focus_handle: cx.focus_handle(),
            job: Job::default(),
            _follows: follows,
        };
        item.build(loaded, cx);
        item
    }

    /// Shows the triage of `loaded` once built in the background, the lines shown staying
    /// until then and the highlight staying on its line while that line is still a link.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The binary to triage.
    /// * `cx` - Item context.
    fn build(&mut self, loaded: Arc<LoadedBinary>, cx: &mut Context<'_, Self>) {
        self.loaded = loaded.clone();
        let name = loaded.path.file_name().unwrap_or(loaded.path.as_os_str());
        let label = format!("Triaging {}", name.to_string_lossy());
        let work = move || rows(&triage_blocking(&loaded), |at| place_at(&loaded, at));
        self.job.run(label, cx, work, |item, rows, cx| {
            let kept = item
                .selected
                .filter(|&ix| rows.get(ix).is_some_and(|r| r.link.is_some()));
            item.selected = kept.or_else(|| rows.iter().position(|row| row.link.is_some()));
            item.rows = rows;
            cx.notify();
        });
    }

    /// Returns the binary the triage is of.
    #[must_use]
    pub const fn loaded(&self) -> &Arc<LoadedBinary> {
        &self.loaded
    }

    /// Returns the lines, empty until the triage is built.
    #[must_use]
    pub fn rows(&self) -> &[Row] {
        &self.rows
    }

    /// Returns the highlighted line.
    #[must_use]
    pub const fn selected(&self) -> Option<usize> {
        self.selected
    }

    /// Moves the highlight to the next link, or the one before, and keeps it in view.
    ///
    /// # Arguments
    ///
    /// * `forward` - Whether to move down.
    /// * `cx` - Item context.
    fn step(&mut self, forward: bool, cx: &mut Context<'_, Self>) {
        let links = self
            .rows
            .iter()
            .enumerate()
            .filter(|(_, r)| r.link.is_some());
        let mut ixs = links.map(|(ix, _)| ix);
        let at = self.selected;
        let next = if forward {
            ixs.find(|&ix| at.is_none_or(|at| ix > at))
        } else {
            ixs.take_while(|&ix| at.is_some_and(|at| ix < at)).last()
        };
        if let Some(ix) = next {
            self.selected = Some(ix);
            self.scroll.scroll_to_item(ix, ScrollStrategy::Nearest);
            cx.notify();
        }
    }

    /// Opens what line `ix` links to in the preview tab, once the current update ends.
    ///
    /// # Arguments
    ///
    /// * `ix` - The line.
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    pub fn follow(&mut self, ix: usize, window: &Window, cx: &mut Context<'_, Self>) {
        let Some((_, place)) = self.rows.get(ix).and_then(|row| row.link.clone()) else {
            return;
        };
        self.selected = Some(ix);
        cx.notify();
        let (workspace, binary) = (self.workspace.clone(), self.binary.clone());
        let loaded = self.loaded.clone();
        window.defer(cx, move |window, cx| {
            let Some(workspace) = workspace.upgrade() else {
                return;
            };
            workspace.update(cx, |workspace, cx| {
                let how = Opening {
                    mode: TabMode::Preview,
                    focus: true,
                };
                open(workspace, &binary, &loaded, place, how, window, cx);
            });
        });
    }

    /// Returns lines `range` drawn.
    ///
    /// # Arguments
    ///
    /// * `range` - The lines to draw.
    /// * `cx` - Item context.
    fn draw(&self, range: Range<usize>, cx: &mut Context<'_, Self>) -> Vec<AnyElement> {
        let selected_bg = cx.theme().colors().element_selected;
        let item = cx.entity().downgrade();
        range
            .filter_map(|ix| Some((ix, self.rows.get(ix)?)))
            .map(|(ix, row)| {
                let color = match (row.look, &row.link) {
                    (_, Some(_)) => Color::Accent,
                    (Look::Heading, None) => Color::Muted,
                    (Look::Warning, None) => Color::Warning,
                    (Look::Plain | Look::Under, None) => Color::Default,
                };
                let size = match row.look {
                    Look::Heading => LabelSize::Small,
                    Look::Plain | Look::Warning | Look::Under => LabelSize::Default,
                };
                let indent = if row.look == Look::Under {
                    INDENT_PX
                } else {
                    0.0
                };
                let item = item.clone();
                let mut line = h_flex()
                    .id(ix)
                    .w_full()
                    .pl(px(8.0 + indent))
                    .pr_2()
                    .gap_2()
                    .children(row.basis.map(|basis| {
                        let (words, color) = basis_label(basis);
                        div()
                            .flex_none()
                            .child(Label::new(words).size(LabelSize::XSmall).color(color))
                    }))
                    .child(
                        Label::new(row.text.clone())
                            .size(size)
                            .color(color)
                            .truncate(),
                    );
                if self.selected == Some(ix) {
                    line = line.bg(selected_bg);
                }
                if row.link.is_some() {
                    line = line.cursor_pointer().on_click(move |_, window, cx| {
                        if let Some(item) = item.upgrade() {
                            item.update(cx, |item, cx| item.follow(ix, window, cx));
                        }
                    });
                }
                line.into_any_element()
            })
            .collect()
    }
}

impl EventEmitter<ItemEvent> for OverviewItem {}

impl Revision for OverviewItem {
    fn revision(&self) -> Option<u64> {
        Some(self.loaded.fingerprint)
    }
}

impl Focusable for OverviewItem {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Item for OverviewItem {
    type Event = ItemEvent;

    fn to_item_events(event: &ItemEvent, f: &mut dyn FnMut(ItemEvent)) {
        f(*event);
    }

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        SharedString::from("Overview")
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::Info))
    }

    crate::app_view::snapshot_tab!();
}

impl Render for OverviewItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let body = if self.rows.is_empty() {
            let says = SharedString::from("Triaging...");
            let card = Card {
                says,
                tone: Tone::Quiet,
                offers: &[],
            };
            card.render(cx)
        } else {
            let draw = cx.processor(|item: &mut Self, range, _window, cx| item.draw(range, cx));
            uniform_list("overview", self.rows.len(), draw)
                .track_scroll(&self.scroll)
                .size_full()
                .into_any_element()
        };
        div()
            .key_context("Overview")
            .track_focus(&self.focus_handle)
            .on_action(cx.listener(|item, _: &menu::SelectNext, _, cx| item.step(true, cx)))
            .on_action(cx.listener(|item, _: &menu::SelectPrevious, _, cx| item.step(false, cx)))
            .on_action(cx.listener(|item, _: &menu::Confirm, window, cx| {
                if let Some(ix) = item.selected {
                    item.follow(ix, window, cx);
                }
            }))
            .size_full()
            .py_2()
            .bg(cx.theme().colors().editor_background)
            .child(body)
    }
}

#[cfg(test)]
impl crate::binary::Digested for OverviewItem {
    fn digest(&self, _cx: &App) -> u64 {
        let d = self
            .rows
            .iter()
            .fold(crate::binary::Digest::default(), |d, row| {
                let marks = format!("{:?} {:?} {:?}", row.look, row.link, row.basis);
                d.text(&row.text).text(&marks)
            });
        d.text(&format!("{:?}", self.selected)).value()
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
pub(crate) mod tests {
    use borer_engine::analysis::render::{
        ReadFirst, Reason, SectionKind, Summary, Triage, TriageSection, triage,
    };
    use borer_engine::crypto::Storage;
    use gpui::{Entity, TestAppContext, VisualContext as _, VisualTestContext};
    use workspace::{ItemHandle, Workspace};

    use super::{OverviewItem, basis_label, rows};
    use crate::app_view::tests::{CALLER, init, open, open_place, sample, shown};
    use crate::decompile_item::{DecompileItem, Form, TabMode};
    use crate::places::{Place, place_of};

    /// Returns a hand-built triage: two sections with addresses, a blind spot and a
    /// function to read first with a reason of every kind.
    pub(crate) fn hand_built() -> Triage {
        let summary = |headline: &str, at: Vec<u64>, at_total| Summary {
            headline: headline.to_owned(),
            count: at.len(),
            at,
            at_total,
        };
        let section = |kind, summary| TriageSection { kind, summary };
        Triage {
            name: "sample.bin".to_owned(),
            shape: "PE x64".to_owned(),
            incomplete: true,
            file: vec!["# not signed".to_owned()],
            sections: vec![
                section(
                    SectionKind::Crypto,
                    summary("crypto: 2 constants", vec![0x10, 0x20], 2),
                ),
                section(
                    SectionKind::Checks,
                    summary("checks: 1 of 5", vec![0x30], 5),
                ),
                section(SectionKind::Iocs, summary("iocs: none", Vec::new(), 0)),
            ],
            blind_spots: vec!["packed".to_owned()],
            read_first: vec![ReadFirst {
                entry: 0x1000,
                name: "main".to_owned(),
                score: 7,
                reasons: vec![
                    Reason::Builds {
                        written_at: 0x50,
                        text: "key".to_owned(),
                    },
                    Reason::Calls {
                        callee: 0x60,
                        name: "connect".to_owned(),
                    },
                    Reason::Holds {
                        at: 0x70,
                        name: "AES",
                        storage: Storage::Native,
                    },
                    Reason::References {
                        strings: 3,
                        imports: 4,
                    },
                ],
            }],
            candidates: 1,
        }
    }

    /// Every link names an address the triage gives, on the line that gives it: each
    /// section's addresses, the function's entry, then each reason's own address.
    #[test]
    fn every_link_is_an_address_the_triage_gives() {
        let place = |at| Some(Place::decompile(at));
        let links: Vec<_> = rows(&hand_built(), place)
            .iter()
            .filter_map(|row| {
                row.link
                    .clone()
                    .map(|(at, link)| (row.text.to_string(), at, link))
            })
            .collect();
        let want = [
            ("0x10", 0x10),
            ("0x20", 0x20),
            ("0x30", 0x30),
            ("main  score 7", 0x1000),
            ("builds \"key\"", 0x50),
            ("calls connect", 0x60),
            ("holds AES", 0x70),
        ];
        let want: Vec<_> = want
            .iter()
            .map(|&(text, at)| (text.to_owned(), at, Place::decompile(at)))
            .collect();
        assert_eq!(links, want);
        assert!(
            rows(&hand_built(), |_| None)
                .iter()
                .all(|row| row.link.is_none())
        );
    }

    /// A read-first list the engine cut short says how many of how many candidates it
    /// shows, under the list, as a section's addresses do; a whole list says nothing.
    #[test]
    fn a_cut_read_first_list_says_how_many_it_shows() {
        let mut triage = hand_built();
        let last = |triage: &Triage| rows(triage, |_| None).last().map(|row| row.text.clone());
        assert_eq!(
            last(&triage).as_deref(),
            Some("references 3 strings and 4 imports")
        );
        let first = triage.read_first[0].clone();
        triage.read_first = vec![first; 10];
        triage.candidates = 25;
        assert_eq!(last(&triage).as_deref(), Some("showing 10 of 25"));
    }

    /// Each reason is labelled with the engine's basis, and no other line is.
    ///
    /// A recovered string reads as observed by running, a call and a count of references
    /// as static, a constant as a pattern match.
    #[test]
    fn every_basis_is_labelled() {
        let labels: Vec<_> = rows(&hand_built(), |_| None)
            .iter()
            .filter_map(|row| Some((row.text.to_string(), basis_label(row.basis?).0)))
            .collect();
        let want = [
            ("builds \"key\"", "observed by running"),
            ("calls connect", "static reference"),
            ("holds AES", "pattern match"),
            ("references 3 strings and 4 imports", "static reference"),
        ];
        let want: Vec<_> = want.iter().map(|&(t, l)| (t.to_owned(), l)).collect();
        assert_eq!(labels, want);
    }

    /// A load opens the overview as the pane's first tab, before the functions panel's
    /// preview of the first function, and its lines hold every section headline of the
    /// engine's triage.
    #[gpui::test]
    fn a_load_opens_the_overview_first(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let binary = app.binary;
        let loaded = sample();
        binary.update(cx, |binary, cx| binary.finish_load(Ok(loaded.clone()), cx));
        cx.run_until_parked();
        let (first, active, text) = workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            let place = |item: Option<&Box<dyn ItemHandle>>| place_of(item?.as_ref(), cx);
            let item = pane.items_of_type::<OverviewItem>().next().unwrap();
            let lines = item.read(cx).rows().iter().map(|row| row.text.to_string());
            let text = lines.collect::<Vec<_>>().join("\n");
            (
                place(pane.items().next()),
                place(pane.active_item().as_ref()),
                text,
            )
        });
        assert_eq!(first, Some(Place::Overview));
        assert_eq!(active, Some(Place::decompile(CALLER)));
        let triage = triage(&loaded.program, &loaded.analysis, &loaded.overlay);
        assert!(!triage.sections.is_empty());
        for section in &triage.sections {
            assert!(text.contains(&section.summary.headline), "{text}");
        }
    }

    /// Opens the overview of the sample in `workspace` and returns it once it is built.
    pub(crate) fn open_overview(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Entity<OverviewItem> {
        open_place(
            workspace,
            &sample(),
            Place::Overview,
            TabMode::Permanent,
            cx,
        );
        cx.run_until_parked();
        workspace.read_with(cx, |workspace, cx| {
            workspace.active_item_as::<OverviewItem>(cx).unwrap()
        })
    }

    /// Walking down to a function to read first and pressing enter opens its decompile; the
    /// sample reads nothing first, so the tab shows the hand-built triage's lines, whose
    /// function is the sample's caller.
    #[gpui::test]
    fn following_a_function_to_read_first_opens_its_decompile(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let item = open_overview(&workspace, cx);
        let first = item.update(cx, |item, _| {
            item.rows = rows(&hand_built(), |at| Some(Place::decompile(at)));
            item.selected = item.rows.iter().position(|r| r.link.is_some());
            let read = item
                .rows
                .iter()
                .position(|r| r.text == "read first")
                .unwrap();
            read + 1
        });
        cx.focus(&item);
        for _ in 0..first {
            if item.read_with(cx, |item, _| item.selected()) != Some(first) {
                cx.dispatch_action(menu::SelectNext);
            }
        }
        assert_eq!(item.read_with(cx, |item, _| item.selected()), Some(first));
        cx.dispatch_action(menu::Confirm);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), Some(CALLER));
        let form = workspace.read_with(cx, |workspace, cx| {
            let tab = workspace.active_item_as::<DecompileItem>(cx).unwrap();
            tab.read(cx).form()
        });
        assert_eq!(form, Form::Decompile);
    }
}
