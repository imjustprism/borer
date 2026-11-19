//! The types panel and the struct tab: every type the engine knows as a rows panel of
//! Zed's right dock, a row opening the type's fields, holes and overlaps in a center tab.

mod edit;

use std::any::Any;
use std::sync::Arc;

use borer_engine::analysis::edit::{Author, Edit, Force, Plan};
use borer_engine::analysis::render::{Proposal, Proposed};
use borer_engine::analysis::utypes::{TypeDetail, TypeKind, TypeRow, TypeRows, TypeSource};
use borer_engine::num::from_usize;
use editor::Editor;
use gpui::prelude::FluentBuilder as _;
use gpui::{
    AnyElement, App, AppContext as _, Context, Entity, EventEmitter, FocusHandle, Focusable,
    InteractiveElement as _, IntoElement, ParentElement as _, Render, SharedString,
    StatefulInteractiveElement as _, Styled as _, Subscription, WeakEntity, Window, div,
    uniform_list,
};
use settings::Settings as _;
use theme::ActiveTheme as _;
use theme_settings::ThemeSettings;
use ui::{Color, Icon, IconName, Label, LabelCommon as _, LabelSize, v_flex};
use workspace::dock::DockPosition;
use workspace::{Item, Pane, Workspace};

pub use self::edit::Ask;
use crate::actions::{
    AcceptProposal, AddField, CopyToUserType, DeleteField, ProposeStruct, RenameField,
    ResizeStruct, RetypeField, ToggleTypes,
};
use crate::app_assets::{AppIcon, Glyph};
use crate::app_view::open_dropped;
use crate::binary::{Binary, BinaryEvent, Revision};
use crate::card::{Card, Tone};
use crate::code_view::Role;
use crate::commands;
use crate::decompile_item::{DecompileItem, Form, TabMode, code_row_height};
use crate::panels::{PanelSpec, remove};
use crate::places::{self, Opening, Place};
use crate::rail::panel;
use crate::rows_panel::{Answer, Empty, RowKind, RowsPanel, add, current, focus};
use crate::table::{Align, Column, Columns, Fit, Ink};
use crate::worker::{
    Job, LoadedBinary, planned_blocking, propose_blocking, type_detail_blocking, type_rows_blocking,
};

/// The types panel's row of [`crate::panels::PANELS`].
pub const PANEL: PanelSpec = PanelSpec {
    key: "Types",
    title: "Types",
    icon: Glyph::App(AppIcon::Types),
    toggle: &ToggleTypes,
    dock: DockPosition::Right,
    docks: &[DockPosition::Left, DockPosition::Right],
    size_px: 480.0,
    hooks: panel::<TypesPanel>(),
    add: add::<Types>,
    remove: remove::<TypesPanel>,
    focus: focus::<Types>,
    current: current::<Types>,
};

/// Every type the engine knows, in a dock.
pub type TypesPanel = RowsPanel<Types>;

/// The engine's types, as rows of a panel.
#[derive(Debug)]
pub struct Types;

/// Returns what a kind of type is called.
///
/// # Arguments
///
/// * `kind` - The engine's kind.
const fn kind_word(kind: TypeKind) -> &'static str {
    match kind {
        TypeKind::Struct => "struct",
        TypeKind::Enum => "enum",
        TypeKind::Typedef => "typedef",
        TypeKind::Interface => "interface",
        TypeKind::Class => "class",
    }
}

/// Returns what a type's source is called.
///
/// # Arguments
///
/// * `source` - The engine's source.
const fn source_word(source: TypeSource) -> &'static str {
    match source {
        TypeSource::User => "user",
        TypeSource::Dwarf => "debug",
        TypeSource::Sdk => "sdk",
        TypeSource::Recovered => "recovered",
    }
}

/// Returns a type's source as the table shows it, with the type a user type shadows.
///
/// # Arguments
///
/// * `row` - The engine's row.
fn source_cell(row: &TypeRow) -> SharedString {
    let source = source_word(row.source);
    row.shadows.map_or_else(
        || source.into(),
        |under| format!("{source}, shadows {}", source_word(under)).into(),
    )
}

/// Returns why the fields of `key` take no edit but a copy, `None` for a user struct.
///
/// # Arguments
///
/// * `key` - The type the tab shows.
fn read_only(key: &TypeKey) -> Option<String> {
    let copy = "Copy to User Type plans a user struct of its fields";
    if key.source != TypeSource::User {
        return Some(format!(
            "{} types are read only: {copy}",
            source_word(key.source)
        ));
    }
    (key.kind != TypeKind::Struct).then(|| {
        let kind = kind_word(key.kind);
        format!(
            "{kind} {} has no fields to edit: only a struct's are",
            key.name
        )
    })
}

/// Returns a count or a size the engine may not know, `?` for one it does not.
///
/// # Arguments
///
/// * `value` - The engine's value.
fn known(value: Option<u64>) -> SharedString {
    value.map_or_else(|| "?".into(), |v| v.to_string().into())
}

/// The type table's columns, in order.
const COLUMNS: [Column<TypeRow>; 6] = [
    Column {
        header: "name",
        cell: |row| row.name.to_string().into(),
        align: Align::Start,
        ink: Ink::Role(Role::Type),
        fit: Fit::Fill,
        sort: Some(|a, b| a.name.cmp(&b.name)),
    },
    Column {
        header: "kind",
        cell: |row| kind_word(row.kind).into(),
        align: Align::Start,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| from_usize(kind_word(row.kind).len())),
        sort: Some(|a, b| kind_word(a.kind).cmp(kind_word(b.kind))),
    },
    Column {
        header: "size",
        cell: |row| known(row.size),
        align: Align::End,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| row.size.unwrap_or(0)),
        sort: Some(|a, b| a.size.cmp(&b.size)),
    },
    Column {
        header: "fields",
        cell: |row| known(row.fields.map(from_usize)),
        align: Align::End,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| row.fields.map_or(0, from_usize)),
        sort: Some(|a, b| a.fields.cmp(&b.fields)),
    },
    Column {
        header: "applied",
        cell: |row| row.applied.to_string().into(),
        align: Align::End,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| from_usize(row.applied)),
        sort: Some(|a, b| a.applied.cmp(&b.applied)),
    },
    Column {
        header: "source",
        cell: source_cell,
        align: Align::Start,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| from_usize(source_cell(row).len())),
        sort: Some(|a, b| source_cell(a).cmp(&source_cell(b))),
    },
];

impl RowKind for Types {
    type Row = TypeRow;
    type Shown = TypeRows;
    type Target = ();
    const PANEL: &'static PanelSpec = &PANEL;
    const PLACEHOLDER: &'static str = "Filter types by name";
    const TABLE: &'static str = "type table";
    const FILTERING: &'static str = "Listing types";

    fn columns(_columns: Columns) -> &'static [Column<TypeRow>] {
        &COLUMNS
    }

    fn warning(_shown: &TypeRows) -> Option<&'static str> {
        None
    }

    fn fetch(loaded: &LoadedBinary, (): &(), filter: &str, limit: usize) -> TypeRows {
        type_rows_blocking(loaded, filter, limit)
    }

    fn nothing(_shown: &TypeRows, query: &SharedString) -> Empty {
        Empty::Nothing(if query.is_empty() {
            "The engine knows no type".into()
        } else {
            format!("No type matches \"{query}\"").into()
        })
    }

    fn place(row: &TypeRow) -> Option<Place> {
        Some(Place::Type(TypeKey {
            name: row.name.to_string().into(),
            source: row.source,
            kind: row.kind,
        }))
    }
}

impl Answer<TypeRow> for TypeRows {
    fn rows(&self) -> &[TypeRow] {
        &self.rows
    }

    fn rows_mut(&mut self) -> &mut [TypeRow] {
        &mut self.rows
    }

    fn total(&self) -> usize {
        self.total
    }

    fn showing(&self) -> SharedString {
        crate::table::count_text(self.rows.len(), self.total, "types").into()
    }
}

/// One type, as its row names it: two types of one name differ by source or kind.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct TypeKey {
    /// The type's name.
    pub name: SharedString,
    /// Where it comes from.
    pub source: TypeSource,
    /// What it is.
    pub kind: TypeKind,
}

/// What a struct tab shows: one type's fields, or the struct a function's accesses
/// through its first argument propose.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Subject {
    /// A type, by its row.
    Type(TypeKey),
    /// The proposal read from the function at this entry.
    Proposal(u64),
}

impl Subject {
    /// Returns the place the tab shows.
    #[must_use]
    pub fn place(&self) -> Place {
        match self {
            Self::Type(key) => Place::Type(key.clone()),
            Self::Proposal(entry) => Place::Proposal { entry: *entry },
        }
    }

    /// Returns what the tab is called.
    #[must_use]
    pub fn title(&self) -> SharedString {
        match self {
            Self::Type(key) => key.name.clone(),
            Self::Proposal(entry) => format!("proposal {entry:#x}").into(),
        }
    }
}

/// One line of a struct tab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Line {
    /// The field at this index of the detail's fields, and whether it shares a byte with
    /// another.
    Field(usize, bool),
    /// A run of bytes no field covers: its offset and length.
    Hole(u64, u64),
    /// The proposed field at this index of the proposal's fields.
    Proposed(usize),
}

/// Returns the lines of `detail` by ascending offset: each field, marked when the engine
/// lists it as overlapping, and each hole.
///
/// # Arguments
///
/// * `detail` - The engine's detail.
#[must_use]
pub fn lines(detail: &TypeDetail) -> Vec<Line> {
    let overlaps = |at: usize| detail.overlaps.iter().any(|&(a, b)| a == at || b == at);
    let fields = detail
        .fields
        .iter()
        .enumerate()
        .map(|(at, f)| (f.offset, Line::Field(at, overlaps(at))));
    let holes = detail
        .holes
        .iter()
        .map(|&(off, len)| (off, Line::Hole(off, len)));
    let mut all: Vec<(u64, Line)> = fields.chain(holes).collect();
    all.sort_by_key(|&(offset, line)| (offset, matches!(line, Line::Field(..))));
    all.into_iter().map(|(_, line)| line).collect()
}

/// What a struct tab holds.
#[derive(Debug)]
enum Shown {
    /// The engine is asked.
    Asking,
    /// The engine lists no such type, or it is a recovered class.
    Missing,
    /// The engine's words for why it proposes nothing.
    Refused(String),
    /// The engine's detail of a type and its lines.
    Detail(Arc<TypeDetail>, Arc<[Line]>),
    /// The engine's proposal and its lines.
    Proposal(Arc<Proposal>, Arc<[Line]>),
}

impl Shown {
    /// Returns the lines shown, none while there is no answer.
    fn lines(&self) -> &[Line] {
        match self {
            Self::Detail(_, lines) | Self::Proposal(_, lines) => lines,
            Self::Asking | Self::Missing | Self::Refused(_) => &[],
        }
    }

    /// Returns the text of `line`.
    ///
    /// # Arguments
    ///
    /// * `line` - A line of what is shown.
    fn text(&self, line: Line) -> String {
        match (self, line) {
            (Self::Detail(detail, _), Line::Field(at, shared)) => {
                detail.fields.get(at).map_or_else(String::new, |f| {
                    let size = known(f.size).to_string();
                    let mark = if shared { "  overlaps" } else { "" };
                    let width = name_width(detail);
                    format!(
                        "{:#06x}  {size:>5}  {:<width$}  {}{mark}",
                        f.offset, f.name, f.ty
                    )
                })
            }
            (_, Line::Hole(offset, len)) => {
                format!("{offset:#06x}  {len:>5}  {len} bytes not covered")
            }
            (Self::Proposal(proposal, _), Line::Proposed(at)) => proposal
                .fields
                .get(at)
                .map_or_else(String::new, proposed_text),
            (_, Line::Field(..) | Line::Proposed(_)) => String::new(),
        }
    }

    /// Returns the color `line` draws in: an overlapping field and a proposed offset read at
    /// more than one width in the theme's warning color, a hole muted.
    ///
    /// # Arguments
    ///
    /// * `line` - A line of what is shown.
    fn color(&self, line: Line) -> Color {
        match (self, line) {
            (_, Line::Field(_, true)) => Color::Warning,
            (_, Line::Hole(..)) => Color::Muted,
            (Self::Proposal(proposal, _), Line::Proposed(at))
                if proposal.fields.get(at).is_some_and(|f| f.widths.len() > 1) =>
            {
                Color::Warning
            }
            (_, Line::Field(_, false) | Line::Proposed(_)) => Color::Default,
        }
    }
}

/// Returns a proposed field's line: its offset from the pointer, every width it is read at,
/// how many instructions read it and whether its address goes to a call.
///
/// # Arguments
///
/// * `f` - The engine's proposed field.
fn proposed_text(f: &Proposed) -> String {
    let sign = if f.offset < 0 { "-" } else { "" };
    let offset = format!("{sign}{:#x}", f.offset.unsigned_abs());
    let widths: Vec<String> = f.widths.iter().map(u32::to_string).collect();
    let widths = if widths.is_empty() {
        "-".to_owned()
    } else {
        widths.join("/")
    };
    let conflict = if f.widths.len() > 1 {
        "  widths differ"
    } else {
        ""
    };
    let passed = if f.passed { "  passed to a call" } else { "" };
    format!(
        "{offset:>7}  {widths:>7}  {} sites{passed}{conflict}",
        f.seen
    )
}

/// Returns the characters the name column takes: the longest field name's.
///
/// # Arguments
///
/// * `detail` - The engine's detail.
fn name_width(detail: &TypeDetail) -> usize {
    let names = detail.fields.iter().map(|f| f.name.chars().count());
    names.max().unwrap_or(0)
}

/// The edits planned, and the engine's plan of them with its dry-run lines, which Enter
/// commits once they are shown, or its refusal.
type Planned = (Vec<Edit>, Result<(Plan, Vec<String>), String>);

/// An edit asked for: what, and once planned, the engine's words for it.
#[derive(Debug)]
struct Draft {
    /// What the person asks.
    ask: Ask,
    /// The edits and the engine's words for them, once planned.
    planned: Option<Planned>,
}

/// A center tab showing one type's fields, holes and overlaps, or a proposal, and the
/// edits planned on it through the engine's edit path.
pub struct StructItem {
    /// Workspace a proposal's site opens in.
    workspace: WeakEntity<Workspace>,
    /// The window's binary, which a drop opens and an edit goes through.
    binary: Entity<Binary>,
    /// The state the tab shows.
    loaded: Arc<LoadedBinary>,
    /// What the tab shows.
    subject: Subject,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
    /// The engine's answer.
    shown: Shown,
    /// Index of the selected line.
    selected: usize,
    /// Zed's single-line editor an edit's text is typed in.
    pub(crate) input: Entity<Editor>,
    /// The edit asked for, if any.
    draft: Option<Draft>,
    /// The request for what the tab shows.
    ask_job: Job,
    /// The request planning the draft.
    plan_job: Job,
    /// Follows the binary's edits.
    _revised: Subscription,
}

impl std::fmt::Debug for StructItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StructItem")
            .field("subject", &self.subject)
            .finish_non_exhaustive()
    }
}

impl StructItem {
    /// Returns the tab showing `subject` of `loaded`, asking the engine in the background.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace a proposal's site opens in.
    /// * `binary` - The window's binary.
    /// * `loaded` - The state to show.
    /// * `subject` - What to show.
    /// * `window` - Window the tab is in.
    /// * `cx` - Tab context.
    #[must_use]
    pub fn new(
        workspace: WeakEntity<Workspace>,
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        subject: Subject,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let input = cx.new(|cx| Editor::single_line(window, cx));
        let revised = cx.subscribe(&binary, |item, _, event: &BinaryEvent, cx| match event {
            BinaryEvent::Revised(loaded) => {
                item.loaded = loaded.clone();
                item.shown = Shown::Asking;
                item.redraft(None);
                item.ask(cx);
            }
            BinaryEvent::Opened(_) | BinaryEvent::Closed | BinaryEvent::Rechecked { .. } => {}
        });
        let mut item = Self {
            workspace,
            binary,
            loaded,
            subject,
            focus_handle: cx.focus_handle(),
            shown: Shown::Asking,
            selected: 0,
            input,
            draft: None,
            ask_job: Job::default(),
            plan_job: Job::default(),
            _revised: revised,
        };
        item.ask(cx);
        item
    }

    /// Asks the engine for what the tab shows over its state, keeping the selection.
    ///
    /// # Arguments
    ///
    /// * `cx` - Tab context.
    fn ask(&mut self, cx: &mut Context<'_, Self>) {
        let (source, subject) = (self.loaded.clone(), self.subject.clone());
        let label = format!("Opening {}", subject.title());
        let work = move || match subject {
            Subject::Type(key) => {
                let detail = type_detail_blocking(&source, &key.name, key.source, key.kind);
                detail.map_or(Shown::Missing, |detail| {
                    let lines = lines(&detail).into();
                    Shown::Detail(Arc::new(detail), lines)
                })
            }
            Subject::Proposal(entry) => match propose_blocking(&source, entry) {
                Ok(proposal) => {
                    let lines = (0..proposal.fields.len()).map(Line::Proposed).collect();
                    Shown::Proposal(Arc::new(proposal), lines)
                }
                Err(why) => Shown::Refused(why),
            },
        };
        self.ask_job.run(label, cx, work, |item, shown, cx| {
            item.shown = shown;
            let last = item.shown.lines().len().saturating_sub(1);
            item.selected = item.selected.min(last);
            cx.notify();
        });
    }

    /// Returns what the tab shows.
    #[must_use]
    pub const fn subject(&self) -> &Subject {
        &self.subject
    }

    /// Returns the snapshot the tab is read from.
    #[must_use]
    pub const fn loaded(&self) -> &Arc<LoadedBinary> {
        &self.loaded
    }

    /// Returns the tab's lines as text, empty until the engine answered.
    #[must_use]
    pub fn texts(&self) -> Vec<String> {
        let lines = self.shown.lines();
        lines.iter().map(|&line| self.shown.text(line)).collect()
    }

    /// Returns the color each line draws in.
    #[must_use]
    pub fn colors(&self) -> Vec<Color> {
        let lines = self.shown.lines();
        lines.iter().map(|&line| self.shown.color(line)).collect()
    }

    /// Returns the engine's dry-run lines of the planned edit, or its refusal, `None`
    /// before an edit is planned.
    #[must_use]
    pub fn said(&self) -> Option<Result<Vec<String>, String>> {
        let (_, planned) = self.draft.as_ref()?.planned.as_ref()?;
        Some(
            planned
                .as_ref()
                .map(|(_, said)| said.clone())
                .map_err(Clone::clone),
        )
    }

    /// Returns the edits planned, empty before an edit is planned.
    #[must_use]
    pub fn planned(&self) -> &[Edit] {
        let planned = self.draft.as_ref().and_then(|d| d.planned.as_ref());
        planned.map_or(&[], |(edits, _)| edits)
    }

    /// Selects line `line`, clamped to the lines shown, and drops the edit asked for.
    ///
    /// # Arguments
    ///
    /// * `line` - Zero-based line index.
    /// * `cx` - Tab context.
    pub fn select(&mut self, line: usize, cx: &mut Context<'_, Self>) {
        self.selected = line.min(self.shown.lines().len().saturating_sub(1));
        self.redraft(None);
        cx.notify();
    }

    /// Starts `ask` on the selected line: a type that is not a user struct is read only but
    /// for a copy, an ask that takes text focuses the input, and one that takes none is
    /// planned at once.
    ///
    /// # Arguments
    ///
    /// * `ask` - What the person asks.
    /// * `window` - Window the tab is in.
    /// * `cx` - Tab context.
    pub fn start(&mut self, ask: Ask, window: &mut Window, cx: &mut Context<'_, Self>) {
        if let Subject::Type(key) = &self.subject
            && ask != Ask::Copy
            && let Some(why) = read_only(key)
        {
            self.redraft(Some(Draft {
                ask,
                planned: Some((Vec::new(), Err(why))),
            }));
            cx.notify();
            return;
        }
        self.redraft(Some(Draft { ask, planned: None }));
        if ask.takes_text() {
            self.input.update(cx, |input, cx| {
                input.set_text("", window, cx);
                input.set_placeholder_text(ask.prompt(), window, cx);
            });
            window.focus(&self.input.focus_handle(cx), cx);
        } else {
            self.plan(window, cx);
        }
        cx.notify();
    }

    /// Puts `draft` in place of the edit asked for, stopping the plan of the one before so
    /// its answer never lands in another draft.
    ///
    /// # Arguments
    ///
    /// * `draft` - The edit now asked for, if any.
    fn redraft(&mut self, draft: Option<Draft>) {
        self.plan_job.stop();
        self.draft = draft;
    }

    /// Plans the edit asked for with the input's text in the background; the engine's
    /// lines or refusal show once it answers.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Tab context.
    fn plan(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let Some(draft) = &mut self.draft else {
            return;
        };
        let line = self.shown.lines().get(self.selected).copied();
        let text = self.input.read(cx).text(cx);
        window.focus(&self.focus_handle, cx);
        let edits = match edit::edits(draft.ask, &self.shown, line, &text) {
            Ok(edits) => edits,
            Err(why) => {
                draft.planned = Some((Vec::new(), Err(why)));
                cx.notify();
                return;
            }
        };
        let (source, asked) = (self.loaded.clone(), edits.clone());
        let work = move || planned_blocking(&source, &asked, Force::Refuse);
        let label = format!("Planning an edit of {}", self.subject.title());
        self.plan_job.run(label, cx, work, move |item, said, cx| {
            if let Some(draft) = &mut item.draft {
                draft.planned = Some((edits, said));
            }
            cx.notify();
        });
    }

    /// Moves the edit on: Enter on a hole adds a field there and on a proposed field opens
    /// its first site; typed text is planned; a plan the engine took commits through the
    /// binary's edit path, the one the agent's tools take.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Tab context.
    pub fn confirm(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        let line = self.shown.lines().get(self.selected).copied();
        let Some(draft) = &mut self.draft else {
            match (line, &self.shown) {
                (Some(Line::Hole(..)), _) => self.start(Ask::Add, window, cx),
                (Some(Line::Proposed(at)), Shown::Proposal(proposal, _)) => {
                    let site = proposal.fields.get(at).and_then(|f| f.sites.first());
                    if let Some(&site) = site {
                        self.open_site(proposal.entry, site, window, cx);
                    }
                }
                (
                    None | Some(Line::Field(..) | Line::Proposed(_)),
                    Shown::Asking
                    | Shown::Missing
                    | Shown::Refused(_)
                    | Shown::Detail(..)
                    | Shown::Proposal(..),
                ) => {}
            }
            return;
        };
        match &draft.planned {
            None => self.plan(window, cx),
            Some((_, Ok(_))) => {
                if let Some(Draft {
                    planned: Some((_, Ok(planned))),
                    ..
                }) = self.draft.take()
                {
                    let shown = crate::worker::Shown::new(planned.0);
                    let heard = self
                        .binary
                        .update(cx, |binary, cx| binary.commit(shown, Author::Person, cx));
                    drop(heard);
                }
            }
            Some((_, Err(_))) => {}
        }
        cx.notify();
    }

    /// Drops the edit asked for.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Tab context.
    pub fn cancel(&mut self, window: &mut Window, cx: &mut Context<'_, Self>) {
        self.redraft(None);
        window.focus(&self.focus_handle, cx);
        cx.notify();
    }

    /// Opens the listing of the function at `entry` at the instruction `site`, once the
    /// current update ends.
    ///
    /// # Arguments
    ///
    /// * `entry` - The function's entry.
    /// * `site` - The instruction's address.
    /// * `window` - Window the tab is in.
    /// * `cx` - Tab context.
    fn open_site(&self, entry: u64, site: u64, window: &Window, cx: &mut Context<'_, Self>) {
        let workspace = self.workspace.clone();
        let (binary, loaded) = (self.binary.clone(), self.loaded.clone());
        let place = Place::Code {
            entry,
            form: Form::Listing,
            at: Some(site),
        };
        window.defer(cx, move |window, cx| {
            if let Some(workspace) = workspace.upgrade() {
                workspace.update(cx, |workspace, cx| {
                    let how = Opening {
                        mode: TabMode::Permanent,
                        focus: true,
                    };
                    places::open(workspace, &binary, &loaded, place, how, window, cx);
                });
            }
        });
    }

    /// Returns what the tab says instead of lines, `None` while it shows them.
    #[must_use]
    pub fn card(&self) -> Option<Card> {
        let title = self.subject.title();
        let kind = match &self.subject {
            Subject::Type(key) => kind_word(key.kind),
            Subject::Proposal(_) => "proposal",
        };
        let recovered =
            matches!(&self.subject, Subject::Type(key) if key.source == TypeSource::Recovered);
        let (says, tone): (SharedString, Tone) = match &self.shown {
            Shown::Asking => (format!("Opening {title}").into(), Tone::Quiet),
            Shown::Missing if recovered => (
                format!("The fields of class {title} come from decompiling its methods").into(),
                Tone::Quiet,
            ),
            Shown::Missing => (
                format!("The engine lists no {kind} {title}").into(),
                Tone::Quiet,
            ),
            Shown::Refused(why) => (why.clone().into(), Tone::Error),
            Shown::Detail(..) | Shown::Proposal(..) if self.shown.lines().is_empty() => (
                format!("The engine lists no fields of {kind} {title}").into(),
                Tone::Quiet,
            ),
            Shown::Detail(..) | Shown::Proposal(..) => return None,
        };
        Some(Card {
            says,
            tone,
            offers: &[],
        })
    }

    /// Returns the head line: the type's source, kind, name and size, or the register and
    /// function a proposal follows.
    fn head(&self) -> String {
        match &self.shown {
            Shown::Detail(detail, _) => {
                let row = &detail.row;
                let (source, kind) = (source_word(row.source), kind_word(row.kind));
                format!("{source} {kind} {}, {} bytes", row.name, known(row.size))
            }
            Shown::Proposal(p, _) => format!(
                "proposed from the accesses through {} in {:#x}; offset, widths, sites",
                p.register, p.entry
            ),
            Shown::Asking | Shown::Missing | Shown::Refused(_) => String::new(),
        }
    }

    /// Returns the draft's rows: the input while text is typed, then the engine's lines or
    /// refusal; `None` without a draft.
    ///
    /// # Arguments
    ///
    /// * `cx` - Tab context.
    fn render_draft(&self, cx: &Context<'_, Self>) -> Option<AnyElement> {
        let draft = self.draft.as_ref()?;
        let typing = draft.planned.is_none() && draft.ask.takes_text();
        let said: Vec<AnyElement> = match &draft.planned {
            Some((_, Ok((_, lines)))) => lines
                .iter()
                .map(String::as_str)
                .chain(std::iter::once("Enter commits, Escape drops"))
                .map(|line| {
                    Label::new(line.to_owned())
                        .size(LabelSize::Small)
                        .into_any_element()
                })
                .collect(),
            Some((_, Err(why))) => {
                vec![
                    Label::new(why.clone())
                        .color(Color::Error)
                        .into_any_element(),
                ]
            }
            None => Vec::new(),
        };
        let draft = v_flex()
            .px_2()
            .py_1()
            .gap_1()
            .border_t_1()
            .border_color(cx.theme().colors().border)
            .when(typing, |d| d.child(self.input.clone()))
            .children(said);
        Some(draft.into_any_element())
    }
}

impl Revision for StructItem {
    fn revision(&self) -> Option<u64> {
        Some(self.loaded.fingerprint)
    }
}

impl EventEmitter<()> for StructItem {}

impl Focusable for StructItem {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Item for StructItem {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        self.subject.title()
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::Blocks))
    }

    fn tab_tooltip_text(&self, _cx: &App) -> Option<SharedString> {
        match &self.subject {
            Subject::Type(key) => {
                let (kind, source) = (kind_word(key.kind), source_word(key.source));
                Some(format!("{source} {kind} {}", key.name).into())
            }
            Subject::Proposal(_) => Some(self.subject.title()),
        }
    }

    fn handle_drop(
        &self,
        _active_pane: &Pane,
        dropped: &dyn Any,
        window: &mut Window,
        cx: &mut App,
    ) -> bool {
        open_dropped(&self.binary, dropped, window, cx)
    }
}

impl Render for StructItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let settings = ThemeSettings::get_global(cx);
        let (font, size) = (settings.buffer_font.clone(), settings.buffer_font_size(cx));
        let selected_bg = cx.theme().colors().element_selected;
        let root = v_flex()
            .key_context("StructItem")
            .track_focus(&self.focus_handle)
            .size_full()
            .bg(cx.theme().colors().editor_background)
            .on_action(cx.listener(|item, _: &menu::SelectNext, _, cx| {
                item.select(item.selected.saturating_add(1), cx);
            }))
            .on_action(cx.listener(|item, _: &menu::SelectPrevious, _, cx| {
                item.select(item.selected.saturating_sub(1), cx);
            }))
            .on_action(cx.listener(|item, _: &menu::Confirm, w, cx| item.confirm(w, cx)))
            .on_action(cx.listener(|item, _: &menu::Cancel, w, cx| item.cancel(w, cx)));
        if let Some(card) = self.card() {
            return root.child(card.render(cx));
        }
        let texts: Arc<[(String, Color)]> = self
            .shown
            .lines()
            .iter()
            .map(|&line| (self.shown.text(line), self.shown.color(line)))
            .collect();
        let (selected, item) = (self.selected, cx.entity().downgrade());
        let list = uniform_list("struct-lines", texts.len(), move |range, _, _| {
            range
                .filter_map(|ix| texts.get(ix).map(|text| (ix, text)))
                .map(|(ix, (text, color))| {
                    let item = item.clone();
                    div()
                        .id(ix)
                        .when(ix == selected, |d| d.bg(selected_bg))
                        .on_click(move |_, _, cx| {
                            if let Some(item) = item.upgrade() {
                                item.update(cx, |item, cx| item.select(ix, cx));
                            }
                        })
                        .child(Label::new(text.clone()).color(*color))
                })
                .collect()
        });
        let head = Label::new(self.head())
            .size(LabelSize::Small)
            .color(Color::Muted);
        root.child(div().px_2().py_1().child(head))
            .child(
                div()
                    .flex_1()
                    .px_2()
                    .font(font)
                    .text_size(size)
                    .line_height(code_row_height(cx))
                    .child(list.size_full()),
            )
            .children(self.render_draft(cx))
    }
}

/// Registers the types panel's and the proposals' workspace actions.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    commands::register(workspace, binary, |w, _: &RenameField, window, cx| {
        ask_active(w, Ask::Rename, window, cx);
    });
    commands::register(workspace, binary, |w, _: &RetypeField, window, cx| {
        ask_active(w, Ask::Retype, window, cx);
    });
    commands::register(workspace, binary, |w, _: &AddField, window, cx| {
        ask_active(w, Ask::Add, window, cx);
    });
    commands::register(workspace, binary, |w, _: &DeleteField, window, cx| {
        ask_active(w, Ask::Delete, window, cx);
    });
    commands::register(workspace, binary, |w, _: &ResizeStruct, window, cx| {
        ask_active(w, Ask::Size, window, cx);
    });
    commands::register(workspace, binary, |w, _: &CopyToUserType, window, cx| {
        ask_active(w, Ask::Copy, window, cx);
    });
    commands::register(workspace, binary, |w, _: &AcceptProposal, window, cx| {
        ask_active(w, Ask::Accept, window, cx);
    });
    let held = binary.clone();
    commands::register(
        workspace,
        binary,
        move |workspace, _: &ProposeStruct, window, cx| {
            let code = workspace.active_item_as::<DecompileItem>(cx);
            let opened = code.and_then(|code| {
                let code = code.read(cx);
                code.entry().map(|entry| (entry, code.loaded().clone()))
            });
            let Some((entry, loaded)) = opened else {
                let why = "open a function's code tab first: its first argument is followed";
                held.update(cx, |binary, cx| binary.set_status(why.to_owned(), cx));
                return;
            };
            let how = Opening {
                mode: TabMode::Permanent,
                focus: true,
            };
            let place = Place::Proposal { entry };
            places::open(workspace, &held, &loaded, place, how, window, cx);
        },
    );
}

/// Starts `ask` on the active struct tab's selected line; with none active it does nothing.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `ask` - What the person asks.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
fn ask_active(
    workspace: &mut Workspace,
    ask: Ask,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    if let Some(item) = workspace.active_item_as::<StructItem>(cx) {
        item.update(cx, |item, cx| item.start(ask, window, cx));
    }
}

#[cfg(test)]
impl crate::binary::Digested for StructItem {
    fn digest(&self, _cx: &App) -> u64 {
        let state = match &self.shown {
            Shown::Asking => "asking",
            Shown::Missing => "missing",
            Shown::Refused(why) => why,
            Shown::Detail(..) => "detail",
            Shown::Proposal(..) => "proposal",
        };
        let d = crate::binary::Digest::default()
            .text(state)
            .num(from_usize(self.selected));
        let lines = self.shown.lines().iter();
        lines
            .fold(d, |d, &line| {
                let color = format!("{:?}", self.shown.color(line));
                d.text(&self.shown.text(line)).text(&color)
            })
            .value()
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use borer_engine::analysis::edit::{self, Edit, Force, Laid};
    use borer_engine::analysis::render::{Proposal, Proposed};
    use borer_engine::analysis::stated::{Field, Mode};
    use borer_engine::analysis::utypes::{
        FieldRow, TypeDetail, TypeExpr, TypeKind, TypeRow, TypeSource, UserField, UserStruct,
        UserType, build_enum, type_detail,
    };
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use ui::Color;
    use workspace::Workspace;

    use super::edit::edits;
    use super::{Ask, Line, Shown, StructItem, TypeKey, Types, TypesPanel, lines};
    use crate::app_view::tests::{CALLEE, CALLER, init, open, open_place, sample};
    use crate::binary::{Binary, BinaryEvent};
    use crate::code_view::Role;
    use crate::decompile_item::TabMode;
    use crate::places::Place;
    use crate::rows_panel::RowKind as _;
    use crate::table::Ink;
    use crate::worker::LoadedBinary;

    /// Returns a field row at `offset`, `size` bytes long.
    fn field(offset: u64, size: u64, name: &str) -> FieldRow {
        FieldRow {
            offset,
            size: Some(size),
            name: name.into(),
            ty: "u32".into(),
        }
    }

    /// Returns a user struct row named `name`.
    fn row(name: &str) -> TypeRow {
        TypeRow {
            name: name.into(),
            kind: TypeKind::Struct,
            size: Some(16),
            fields: Some(3),
            applied: 0,
            source: TypeSource::User,
            shadows: None,
        }
    }

    /// Returns the shown detail of `detail`, with its lines.
    fn shown(detail: TypeDetail) -> Shown {
        let lines = lines(&detail).into();
        Shown::Detail(Arc::new(detail), lines)
    }

    /// Fields and holes interleave by offset, a hole names its bytes, and only the fields
    /// the engine pairs as overlapping are marked.
    #[test]
    fn lines_interleave_fields_and_holes_and_mark_overlaps() {
        let detail = TypeDetail {
            row: row("S"),
            fields: vec![field(0, 4, "a"), field(8, 4, "b"), field(8, 2, "c")],
            holes: vec![(4, 4), (12, 4)],
            overlaps: vec![(1, 2)],
        };
        let got = lines(&detail);
        assert_eq!(
            got,
            [
                Line::Field(0, false),
                Line::Hole(4, 4),
                Line::Field(1, true),
                Line::Field(2, true),
                Line::Hole(12, 4),
            ]
        );
        let shown = shown(detail);
        let text = |line| shown.text(line);
        assert_eq!(text(Line::Hole(4, 4)), "0x0004      4  4 bytes not covered");
        assert_eq!(text(Line::Field(0, false)), "0x0000      4  a  u32");
        assert!(text(Line::Field(1, true)).ends_with("overlaps"));
        assert_eq!(shown.color(Line::Field(1, true)), Color::Warning);
    }

    /// A row opens its own type by name, source and kind, a user type's source says what
    /// it shadows, and a missing size or count reads `?`.
    #[test]
    fn a_type_row_names_its_place_and_its_source() {
        let mut user = row("S");
        user.shadows = Some(TypeSource::Dwarf);
        user.size = None;
        let want = TypeKey {
            name: "S".into(),
            source: TypeSource::User,
            kind: TypeKind::Struct,
        };
        assert_eq!(Types::place(&user), Some(Place::Type(want)));
        let cells: Vec<_> = super::COLUMNS.iter().map(|c| (c.cell)(&user)).collect();
        assert_eq!(cells, ["S", "struct", "?", "3", "0", "user, shadows debug"]);
    }

    /// The name column draws in the theme's type color, the others muted.
    #[test]
    fn type_names_draw_in_the_type_color() {
        let inks: Vec<Ink> = super::COLUMNS.iter().map(|c| c.ink).collect();
        assert_eq!(inks.first(), Some(&Ink::Role(Role::Type)));
        assert!(
            inks.iter().skip(1).all(|ink| *ink == Ink::Muted),
            "{inks:?}"
        );
    }

    /// Returns `base` with a user struct `S` of a `u32` `a` at 0 and one `b` at 8, 16
    /// bytes long, and a debug struct `D` of the same fields.
    fn with_structs(base: &LoadedBinary) -> Arc<LoadedBinary> {
        let at = |name: &str| UserField {
            name: name.to_owned(),
            ty: TypeExpr::U32,
        };
        let fields = BTreeMap::from([(0, at("a")), (8, at("b"))]);
        let s = UserType::Struct(UserStruct { size: 16, fields });
        let mut program = (*base.program).clone();
        program.debug_types.insert("D".to_owned(), s.clone());
        let mut overlay = (*base.overlay).clone();
        overlay.types.insert("S".to_owned(), s);
        let edited = base.with_overlay(overlay);
        Arc::new(LoadedBinary {
            path: edited.path.clone(),
            program: Arc::new(program),
            analysis: edited.analysis.clone(),
            overlay: edited.overlay.clone(),
            initial_rows: edited.initial_rows.clone(),
            notes: Vec::new(),
            identity: String::new(),
            fingerprint: edited.fingerprint,
        })
    }

    /// Go to's Enter on a type's hit shows the types panel filtered to the type's name, so
    /// each source and kind of that name is listed to open.
    #[gpui::test]
    fn going_to_a_type_lists_it_in_the_types_panel(cx: &mut TestAppContext) {
        let (workspace, _, _, cx) = loaded_with_structs(cx);
        cx.dispatch_action(crate::goto::GoTo);
        cx.run_until_parked();
        let picker = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_modal::<picker::Picker<crate::goto::GoToDelegate>>(cx)
            })
            .unwrap();
        picker.update_in(cx, |picker, window, cx| picker.set_query("t:S", window, cx));
        cx.run_until_parked();
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        let filter = workspace.read_with(cx, |workspace, cx| {
            workspace
                .panel::<TypesPanel>(cx)
                .map(|panel| panel.read(cx).filter_text(cx))
        });
        assert_eq!(filter.as_deref(), Some("S"));
    }

    /// Returns the window's binary, loaded with [`with_structs`] over the sample, and its
    /// workspace.
    fn loaded_with_structs(
        cx: &mut TestAppContext,
    ) -> (
        Entity<Workspace>,
        Entity<Binary>,
        Arc<LoadedBinary>,
        &mut VisualTestContext,
    ) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let loaded = with_structs(&sample());
        app.binary
            .update(cx, |binary, cx| binary.show_loaded(loaded.clone(), cx));
        cx.run_until_parked();
        (app.workspace.clone(), app.binary.clone(), loaded, cx)
    }

    /// Returns the struct tab active in `workspace` once `place` of `loaded` is open.
    fn struct_tab(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        place: Place,
        cx: &mut VisualTestContext,
    ) -> Entity<StructItem> {
        open_place(workspace, loaded, place, TabMode::Permanent, cx);
        cx.run_until_parked();
        workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<StructItem>(cx)
            })
            .unwrap()
    }

    /// Returns the place of the struct `name` from `source`.
    fn type_place(name: &str, source: TypeSource) -> Place {
        Place::Type(TypeKey {
            name: name.into(),
            source,
            kind: TypeKind::Struct,
        })
    }

    /// Types `text` in the tab's input and presses Enter, then lets the engine answer.
    fn type_and_confirm(item: &Entity<StructItem>, text: &str, cx: &mut VisualTestContext) {
        item.update_in(cx, |item, window, cx| {
            item.input
                .update(cx, |input, cx| input.set_text(text, window, cx));
            item.confirm(window, cx);
        });
        cx.run_until_parked();
    }

    /// A loaded binary's types list in the panel without opening a tab, and the user
    /// struct's row opens one tab of its fields and holes, from the engine's detail.
    #[gpui::test]
    fn the_types_panel_lists_a_struct_and_opens_its_fields(cx: &mut TestAppContext) {
        let (workspace, _, loaded, cx) = loaded_with_structs(cx);
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<TypesPanel>(window, cx);
        });
        cx.run_until_parked();
        let panel = workspace
            .read_with(cx, |workspace, cx| workspace.panel::<TypesPanel>(cx))
            .unwrap();
        let names = panel.read_with(cx, |panel, _| {
            panel.rows().map(|rows| {
                rows.rows
                    .iter()
                    .map(|r| r.name.to_string())
                    .collect::<Vec<_>>()
            })
        });
        assert!(names.unwrap().contains(&"S".to_owned()));
        let place = type_place("S", TypeSource::User);
        struct_tab(&workspace, &loaded, place.clone(), cx);
        let item = struct_tab(&workspace, &loaded, place, cx);
        let tabs = workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            pane.items_of_type::<StructItem>().count()
        });
        assert_eq!(tabs, 1);
        assert_eq!(
            item.read_with(cx, |item, _| item.texts()),
            [
                "0x0000      4  a  u32",
                "0x0004      4  4 bytes not covered",
                "0x0008      4  b  u32",
                "0x000c      4  4 bytes not covered",
            ]
        );
    }

    /// Renaming a field shows the engine's dry-run lines, then Enter commits one change
    /// through the binary's edit path: the overlay and the engine's detail name the field
    /// anew, and the tab shows the state the edit left.
    #[gpui::test]
    fn renaming_a_field_commits_through_the_edit_path(cx: &mut TestAppContext) {
        let (workspace, binary, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, type_place("S", TypeSource::User), cx);
        item.update_in(cx, |item, window, cx| item.start(Ask::Rename, window, cx));
        type_and_confirm(&item, "x", cx);
        let said = item.read_with(cx, |item, _| item.said());
        let said = said.unwrap().unwrap();
        assert!(said.iter().any(|line| line.contains('x')), "{said:?}");
        item.update_in(cx, |item, window, cx| item.confirm(window, cx));
        cx.run_until_parked();
        let now = binary.read_with(cx, |binary, _| binary.loaded().cloned().unwrap());
        assert_ne!(now.fingerprint, loaded.fingerprint);
        let (p, a, o) = (&*now.program, &*now.analysis, &*now.overlay);
        let detail = type_detail(p, a, o, "S", TypeSource::User, TypeKind::Struct).unwrap();
        let names: Vec<&str> = detail.fields.iter().map(|f| &*f.name).collect();
        assert_eq!(names, ["x", "b"]);
        let (texts, revision) = item.read_with(cx, |item, _| {
            use crate::binary::Revision as _;
            (item.texts(), item.revision())
        });
        assert_eq!(
            texts.first().map(String::as_str),
            Some("0x0000      4  x  u32")
        );
        assert_eq!(revision, Some(now.fingerprint));
    }

    /// A plan that lands after its draft was dropped fills no later draft: Delete on `a`,
    /// then a move and Rename before Delete's plan lands, leaves nothing planned.
    #[gpui::test]
    fn a_plan_lands_only_in_its_own_draft(cx: &mut TestAppContext) {
        let (workspace, _, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, type_place("S", TypeSource::User), cx);
        item.update_in(cx, |item, window, cx| {
            item.start(Ask::Delete, window, cx);
            item.select(1, cx);
            item.start(Ask::Rename, window, cx);
        });
        cx.run_until_parked();
        let planned = item.read_with(cx, |item, _| item.planned().to_vec());
        assert!(planned.is_empty(), "{planned:?}");
    }

    /// An edit asked after the binary was revised, before the tab's new detail lands, is not
    /// planned from the lines shown before.
    #[gpui::test]
    fn an_edit_after_a_revision_waits_for_the_new_lines(cx: &mut TestAppContext) {
        let (workspace, binary, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, type_place("S", TypeSource::User), cx);
        binary.update(cx, |_, cx| cx.emit(BinaryEvent::Revised(loaded.clone())));
        item.update_in(cx, |item, window, cx| item.start(Ask::Delete, window, cx));
        cx.run_until_parked();
        let planned = item.read_with(cx, |item, _| item.planned().to_vec());
        assert!(planned.is_empty(), "{planned:?}");
    }

    /// A debug type opens read only, saying so in place of a plan, and Copy to User Type
    /// plans a user struct whose fields are the debug type's.
    #[gpui::test]
    fn a_debug_type_is_read_only_and_copies_to_a_user_struct(cx: &mut TestAppContext) {
        let (workspace, _, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, type_place("D", TypeSource::Dwarf), cx);
        item.update_in(cx, |item, window, cx| item.start(Ask::Rename, window, cx));
        let refused = item.read_with(cx, |item, _| item.said());
        assert!(refused.unwrap().unwrap_err().contains("read only"));
        item.update_in(cx, |item, window, cx| item.start(Ask::Copy, window, cx));
        type_and_confirm(&item, "DCopy", cx);
        let (planned, said) = item.read_with(cx, |item, _| (item.planned().to_vec(), item.said()));
        let [
            Edit::Fields {
                name, fields, mode, ..
            },
        ] = planned.as_slice()
        else {
            panic!("{planned:?}");
        };
        assert_eq!((name.as_str(), *mode), ("DCopy", Mode::Replace));
        let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
        let debug = type_detail(p, a, o, "D", TypeSource::Dwarf, TypeKind::Struct).unwrap();
        let want: Vec<(u64, String)> = debug
            .fields
            .iter()
            .map(|f| (f.offset, f.name.to_string()))
            .collect();
        let got: Vec<(u64, String)> = fields.iter().map(|(o, f)| (*o, f.name.clone())).collect();
        assert_eq!(got, want);
        assert!(said.unwrap().is_ok());
    }

    /// A user enum lists none of its bytes as not covered, and no ask but a copy plans an
    /// edit of it: each says why in place of a plan.
    #[gpui::test]
    fn a_user_enum_takes_no_field_edit(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let base = sample();
        let mut overlay = (*base.overlay).clone();
        let e = build_enum("E", 4, &[(1, "One".to_owned())]).unwrap();
        overlay.types.insert("E".to_owned(), e);
        let loaded = base.with_overlay(overlay);
        app.binary
            .update(cx, |binary, cx| binary.show_loaded(loaded.clone(), cx));
        cx.run_until_parked();
        let place = Place::Type(TypeKey {
            name: "E".into(),
            source: TypeSource::User,
            kind: TypeKind::Enum,
        });
        let item = struct_tab(&app.workspace, &loaded, place, cx);
        let texts = item.read_with(cx, |item, _| item.texts());
        assert!(
            !texts.iter().any(|t| t.contains("not covered")),
            "{texts:?}"
        );
        for ask in [Ask::Add, Ask::Rename, Ask::Retype, Ask::Delete, Ask::Size] {
            item.update_in(cx, |item, window, cx| item.start(ask, window, cx));
            cx.run_until_parked();
            let said = item.read_with(cx, |item, _| item.said());
            assert!(matches!(said, Some(Err(_))), "{ask:?}: {said:?}");
        }
    }

    /// Returns a proposal of a pointer read at two widths at offset 0 and one at 8.
    fn two_widths() -> Proposal {
        let at = |offset, widths: Vec<u32>| Proposed {
            offset,
            widths,
            sites: vec![0x1004],
            seen: 1,
            passed: false,
        };
        Proposal {
            entry: CALLER,
            register: "rcx".to_owned(),
            param: Some(0),
            fields: vec![at(0, vec![2, 4]), at(8, vec![8])],
        }
    }

    /// A proposed offset read at two widths is marked in the theme's warning color and says
    /// the widths differ, the other is not; accepting it plans the agent's layout request,
    /// and the lines a proposal tab shows for it are the engine's plan of that request.
    #[gpui::test]
    fn a_proposal_marks_a_width_conflict_and_accept_plans_its_layout(cx: &mut TestAppContext) {
        let proposal = two_widths();
        let lines = (0..proposal.fields.len()).map(Line::Proposed).collect();
        let shown = Shown::Proposal(Arc::new(proposal), lines);
        assert_eq!(shown.color(Line::Proposed(0)), Color::Warning);
        assert_eq!(shown.color(Line::Proposed(1)), Color::Default);
        assert!(shown.text(Line::Proposed(0)).ends_with("widths differ"));
        let planned = edits(Ask::Accept, &shown, None, "Obj").unwrap();
        let [Edit::Layout { from, name }] = planned.as_slice() else {
            panic!("{planned:?}");
        };
        assert_eq!(
            (from, name.as_str()),
            (&Laid::Pointer(format!("{CALLER:#x},rcx")), "Obj")
        );
        let (workspace, _, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, Place::Proposal { entry: CALLER }, cx);
        item.update_in(cx, |item, window, cx| item.start(Ask::Accept, window, cx));
        type_and_confirm(&item, "Obj", cx);
        let (planned, said) = item.read_with(cx, |item, _| (item.planned().to_vec(), item.said()));
        let (p, a, o) = (&*loaded.program, &*loaded.analysis, &*loaded.overlay);
        let want = edit::plan(p, a, o, &planned, Force::Refuse)
            .map(|plan| {
                plan.lines()
                    .iter()
                    .map(|l| l.said(true).0)
                    .collect::<Vec<_>>()
            })
            .map_err(|e| format!("{e:#}"));
        assert!(
            matches!(planned.as_slice(), [Edit::Layout { .. }]),
            "{planned:?}"
        );
        assert_eq!(said, Some(want));
    }

    /// Accepting the proposal of a function that reads through its first argument is
    /// planned by the engine, and Enter commits it: the overlay holds the struct named.
    #[gpui::test]
    fn accepting_a_proposal_commits_its_struct(cx: &mut TestAppContext) {
        let (workspace, binary, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, Place::Proposal { entry: CALLEE }, cx);
        let texts = item.read_with(cx, |item, _| item.texts());
        assert!(!texts.is_empty(), "the callee reads through rcx");
        item.update_in(cx, |item, window, cx| item.start(Ask::Accept, window, cx));
        type_and_confirm(&item, "Obj", cx);
        let said = item.read_with(cx, |item, _| item.said());
        assert!(matches!(said, Some(Ok(_))), "{said:?}");
        item.update_in(cx, |item, window, cx| item.confirm(window, cx));
        cx.run_until_parked();
        let now = binary.read_with(cx, |binary, _| binary.loaded().cloned().unwrap());
        let obj = now.overlay.types.get("Obj");
        assert!(matches!(obj, Some(UserType::Struct(_))), "{obj:?}");
    }

    /// Asks `ask` on line `line` of the struct tab with `text` typed, checks the engine took
    /// the plan and commits it, returning the dry-run lines and the binary's state after.
    fn commit(
        item: &Entity<StructItem>,
        binary: &Entity<Binary>,
        (ask, line, text): (Ask, usize, &str),
        cx: &mut VisualTestContext,
    ) -> (Vec<String>, Arc<LoadedBinary>) {
        item.update_in(cx, |item, window, cx| {
            item.select(line, cx);
            item.start(ask, window, cx);
        });
        if ask.takes_text() {
            type_and_confirm(item, text, cx);
        }
        cx.run_until_parked();
        let said = item.read_with(cx, |item, _| item.said());
        let said = said.unwrap().unwrap_or_else(|why| panic!("{ask:?}: {why}"));
        item.update_in(cx, |item, window, cx| item.confirm(window, cx));
        cx.run_until_parked();
        (
            said,
            binary.read_with(cx, |binary, _| binary.loaded().cloned().unwrap()),
        )
    }

    /// Rename, Retype, Size and Delete each commit through the edit path, and the engine's
    /// detail after each shows the field or size asked for.
    #[gpui::test]
    fn each_field_edit_commits_what_was_asked(cx: &mut TestAppContext) {
        let (workspace, binary, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, type_place("S", TypeSource::User), cx);
        let detail = |now: &LoadedBinary| {
            let (p, a, o) = (&*now.program, &*now.analysis, &*now.overlay);
            type_detail(p, a, o, "S", TypeSource::User, TypeKind::Struct).unwrap()
        };
        let fields = |now: &LoadedBinary| -> Vec<(u64, String, String)> {
            let detail = detail(now);
            let fields = detail.fields.iter();
            fields
                .map(|f| (f.offset, f.name.to_string(), f.ty.to_string()))
                .collect()
        };
        let (said, now) = commit(&item, &binary, (Ask::Rename, 0, "x"), cx);
        assert!(
            said.iter().any(|l| l.contains("a u32 -> x u32")),
            "{said:?}"
        );
        let (x, b) = ((0, "x".to_owned(), "u32".to_owned()), (8, "b".to_owned()));
        assert_eq!(
            fields(&now),
            [x.clone(), (b.0, b.1.clone(), "u32".to_owned())]
        );
        let (_, now) = commit(&item, &binary, (Ask::Retype, 2, "u16"), cx);
        let retyped = (b.0, b.1, "u16".to_owned());
        assert_eq!(fields(&now), [x, retyped.clone()]);
        let (_, now) = commit(&item, &binary, (Ask::Size, 0, "0x20"), cx);
        assert_eq!(detail(&now).row.size, Some(0x20));
        let (_, now) = commit(&item, &binary, (Ask::Delete, 0, ""), cx);
        assert_eq!(fields(&now), [retyped]);
        assert_eq!(detail(&now).row.size, Some(0x20));
    }

    /// Enter on a hole starts adding a field there, and the field planned sits at the
    /// hole's offset with the name and type typed.
    #[gpui::test]
    fn a_hole_plans_a_field_at_its_offset(cx: &mut TestAppContext) {
        let detail = TypeDetail {
            row: row("S"),
            fields: vec![field(0, 4, "a")],
            holes: vec![(4, 12)],
            overlaps: Vec::new(),
        };
        let planned = edits(Ask::Add, &shown(detail), Some(Line::Hole(4, 12)), "n u16").unwrap();
        let [
            Edit::Fields {
                name, fields, mode, ..
            },
        ] = planned.as_slice()
        else {
            panic!("{planned:?}");
        };
        assert_eq!((name.as_str(), *mode), ("S", Mode::Merge));
        let want = Field {
            name: "n".to_owned(),
            ty: Some(TypeExpr::U16),
        };
        assert_eq!(fields.as_slice(), [(4, want)]);
        let (workspace, _, loaded, cx) = loaded_with_structs(cx);
        let item = struct_tab(&workspace, &loaded, type_place("S", TypeSource::User), cx);
        item.update_in(cx, |item, window, cx| {
            item.select(1, cx);
            item.confirm(window, cx);
        });
        type_and_confirm(&item, "n u16", cx);
        let planned = item.read_with(cx, |item, _| item.planned().to_vec());
        let [Edit::Fields { fields, .. }] = planned.as_slice() else {
            panic!("{planned:?}");
        };
        assert_eq!(fields.first().map(|(offset, _)| *offset), Some(4));
    }

    /// A size is decimal or hex after `0x`: `1a` is no size, `26` and `0x1a` are 26 bytes.
    #[test]
    fn a_size_reads_as_decimal_or_0x_hex() {
        let detail = TypeDetail {
            row: row("S"),
            fields: vec![field(0, 4, "a")],
            holes: Vec::new(),
            overlaps: Vec::new(),
        };
        let shown = shown(detail);
        assert!(edits(Ask::Size, &shown, None, "1a").is_err());
        for text in ["26", "0x1a"] {
            let planned = edits(Ask::Size, &shown, None, text).unwrap();
            let [Edit::Fields { size, .. }] = planned.as_slice() else {
                panic!("{planned:?}");
            };
            assert_eq!(*size, Some(26), "{text}");
        }
    }

    /// No code of the types panel or the struct tab writes an overlay: every edit is an
    /// engine plan, committed by the binary's edit path.
    #[test]
    fn no_struct_edit_writes_the_overlay() {
        let kept = |text: &'static str| text.find("mod tests {").map_or(text, |at| &text[..at]);
        for (name, text) in [
            ("types.rs", kept(include_str!("types.rs"))),
            ("types/edit.rs", kept(include_str!("types/edit.rs"))),
        ] {
            for write in [
                "edit::commit(",
                ".types.insert(",
                ".applied.insert(",
                "overlay =",
                "Overlay::",
                "with_overlay(",
                ".assign(",
            ] {
                assert!(!text.contains(write), "{name} names {write}");
            }
        }
    }
}
