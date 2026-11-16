//! The types panel and the struct tab: every type the engine knows as a rows panel of
//! Zed's right dock, a row opening the type's fields, holes and overlaps in a center tab.

use std::any::Any;
use std::sync::Arc;

use borer_engine::analysis::utypes::{TypeDetail, TypeKind, TypeRow, TypeRows, TypeSource};
use borer_engine::num::from_usize;
use gpui::{
    App, Context, Entity, EventEmitter, FocusHandle, Focusable, InteractiveElement as _,
    IntoElement, ParentElement as _, Render, SharedString, Styled as _, Window, div, uniform_list,
};
use settings::Settings as _;
use theme::ActiveTheme as _;
use theme_settings::ThemeSettings;
use ui::{Color, Icon, IconName, Label, LabelCommon as _, LabelSize, v_flex};
use workspace::dock::DockPosition;
use workspace::{Item, Pane};

use crate::actions::ToggleTypes;
use crate::app_assets::{AppIcon, Glyph};
use crate::app_view::open_dropped;
use crate::binary::Binary;
use crate::card::{Card, Tone};
use crate::code_view::Role;
use crate::decompile_item::code_row_height;
use crate::panels::{PanelSpec, remove};
use crate::places::Place;
use crate::rail::panel;
use crate::rows_panel::{Answer, Empty, RowKind, RowsPanel, add, focus};
use crate::table::{Align, Column, Columns, Fit, Ink};
use crate::worker::{Job, LoadedBinary, type_detail_blocking, type_rows_blocking};

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
        ink: Ink::Role(Role::Function),
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
        format!("showing {} of {} types", self.rows.len(), self.total).into()
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

/// One line of a struct tab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Line {
    /// The field at this index of the detail's fields, and whether it shares a byte with
    /// another.
    Field(usize, bool),
    /// A run of bytes no field covers: its offset and length.
    Hole(u64, u64),
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

/// Returns the text of `line` of `detail`, its name padded to `width` characters.
///
/// # Arguments
///
/// * `detail` - The engine's detail.
/// * `line` - The line.
/// * `width` - Characters the name column takes.
#[must_use]
pub fn line_text(detail: &TypeDetail, line: Line, width: usize) -> String {
    match line {
        Line::Field(at, shared) => detail.fields.get(at).map_or_else(String::new, |f| {
            let size = known(f.size).to_string();
            let mark = if shared { "  overlaps" } else { "" };
            format!(
                "{:#06x}  {size:>5}  {:<width$}  {}{mark}",
                f.offset, f.name, f.ty
            )
        }),
        Line::Hole(offset, len) => format!("{offset:#06x}  {len:>5}  {len} bytes not covered"),
    }
}

/// What a struct tab holds.
#[derive(Debug)]
enum Shown {
    /// The engine is asked for the detail.
    Asking,
    /// The engine lists no such type, or it is a recovered class.
    Missing,
    /// The engine's detail and its lines.
    Detail(Arc<TypeDetail>, Arc<[Line]>),
}

/// A center tab showing one type's fields, holes and overlaps, read only.
pub struct StructItem {
    /// The window's binary, which a drop opens.
    binary: Entity<Binary>,
    /// The snapshot the type is read from.
    loaded: Arc<LoadedBinary>,
    /// The type shown.
    key: TypeKey,
    /// Focus handle of the tab.
    focus_handle: FocusHandle,
    /// What the tab shows.
    shown: Shown,
    /// The request for the detail, held so closing the tab stops it.
    _job: Job,
}

impl std::fmt::Debug for StructItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StructItem")
            .field("key", &self.key)
            .finish_non_exhaustive()
    }
}

impl StructItem {
    /// Returns the tab showing the type `key` of `loaded`, asking the engine for it in the
    /// background.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary, which a drop opens.
    /// * `loaded` - The snapshot the type is read from.
    /// * `key` - The type.
    /// * `_window` - Window the tab is in.
    /// * `cx` - Tab context.
    #[must_use]
    pub fn new(
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        key: TypeKey,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let mut job = Job::default();
        let (source, asked) = (loaded.clone(), key.clone());
        let work = move || {
            type_detail_blocking(&source, &asked.name, asked.source, asked.kind).map(Arc::new)
        };
        job.run(
            format!("Opening {}", key.name),
            cx,
            work,
            |item, detail, cx| {
                item.shown = detail.map_or(Shown::Missing, |detail| {
                    let lines = lines(&detail).into();
                    Shown::Detail(detail, lines)
                });
                cx.notify();
            },
        );
        Self {
            binary,
            loaded,
            key,
            focus_handle: cx.focus_handle(),
            shown: Shown::Asking,
            _job: job,
        }
    }

    /// Returns the snapshot the type is read from.
    #[must_use]
    pub const fn loaded(&self) -> &Arc<LoadedBinary> {
        &self.loaded
    }

    /// Returns the type the tab shows.
    #[must_use]
    pub const fn key(&self) -> &TypeKey {
        &self.key
    }

    /// Returns the tab's lines as text, empty until the engine answered.
    #[must_use]
    pub fn texts(&self) -> Vec<String> {
        let Shown::Detail(detail, lines) = &self.shown else {
            return Vec::new();
        };
        let width = name_width(detail);
        lines.iter().map(|&l| line_text(detail, l, width)).collect()
    }

    /// Returns what the tab says instead of lines, `None` while it shows them.
    #[must_use]
    pub fn card(&self) -> Option<Card> {
        let (name, kind) = (&self.key.name, kind_word(self.key.kind));
        let says: SharedString = match &self.shown {
            Shown::Asking => format!("Opening {name}").into(),
            Shown::Missing if self.key.source == TypeSource::Recovered => {
                format!("The fields of class {name} come from decompiling its methods").into()
            }
            Shown::Missing => format!("The engine lists no {kind} {name}").into(),
            Shown::Detail(_, lines) if lines.is_empty() => {
                format!("The engine lists no fields of {kind} {name}").into()
            }
            Shown::Detail(..) => return None,
        };
        Some(Card {
            says,
            tone: Tone::Quiet,
            offers: &[],
        })
    }
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

impl EventEmitter<()> for StructItem {}

impl Focusable for StructItem {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Item for StructItem {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        self.key.name.clone()
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::Blocks))
    }

    fn tab_tooltip_text(&self, _cx: &App) -> Option<SharedString> {
        let (kind, source) = (kind_word(self.key.kind), source_word(self.key.source));
        Some(format!("{source} {kind} {}", self.key.name).into())
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
        let root = v_flex()
            .track_focus(&self.focus_handle)
            .size_full()
            .bg(cx.theme().colors().editor_background);
        if let Some(card) = self.card() {
            return root.child(card.render(cx));
        }
        let Shown::Detail(detail, lines) = &self.shown else {
            return root;
        };
        let row = &detail.row;
        let head = format!(
            "{} {} {}, {} bytes",
            source_word(row.source),
            kind_word(row.kind),
            row.name,
            known(row.size)
        );
        let (detail, lines) = (detail.clone(), lines.clone());
        let width = name_width(&detail);
        let list = uniform_list("struct-lines", lines.len(), move |range, _, _| {
            range
                .filter_map(|ix| lines.get(ix).copied())
                .map(|line| {
                    let color = match line {
                        Line::Field(_, true) => Color::Warning,
                        Line::Field(_, false) => Color::Default,
                        Line::Hole(..) => Color::Muted,
                    };
                    Label::new(line_text(&detail, line, width)).color(color)
                })
                .collect()
        });
        root.child(
            div()
                .px_2()
                .py_1()
                .child(Label::new(head).size(LabelSize::Small).color(Color::Muted)),
        )
        .child(
            div()
                .flex_1()
                .px_2()
                .font(font)
                .text_size(size)
                .line_height(code_row_height(cx))
                .child(list.size_full()),
        )
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

    use borer_engine::analysis::utypes::{
        FieldRow, TypeDetail, TypeExpr, TypeKind, TypeRow, TypeSource, UserField, UserStruct,
        UserType,
    };
    use gpui::TestAppContext;

    use super::{Line, StructItem, TypeKey, Types, TypesPanel, line_text, lines};
    use crate::app_view::tests::{init, open, open_place, sample};
    use crate::decompile_item::TabMode;
    use crate::places::Place;
    use crate::rows_panel::RowKind as _;
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
        assert_eq!(
            line_text(&detail, Line::Hole(4, 4), 1),
            "0x0004      4  4 bytes not covered"
        );
        assert_eq!(
            line_text(&detail, Line::Field(0, false), 1),
            "0x0000      4  a  u32"
        );
        assert!(line_text(&detail, Line::Field(1, true), 1).ends_with("overlaps"));
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

    /// Returns the sample binary with a user struct `S` of a `u32` at 0 and one at 8, 16
    /// bytes long.
    fn with_struct() -> Arc<LoadedBinary> {
        let base = sample();
        let mut overlay = (*base.overlay).clone();
        let at = |name: &str| UserField {
            name: name.to_owned(),
            ty: TypeExpr::U32,
        };
        let fields = BTreeMap::from([(0, at("a")), (8, at("b"))]);
        overlay.types.insert(
            "S".to_owned(),
            UserType::Struct(UserStruct { size: 16, fields }),
        );
        base.with_overlay(overlay)
    }

    /// A loaded binary's types list in the panel without opening a tab, and the user
    /// struct's row opens one tab of its fields and holes, from the engine's detail.
    #[gpui::test]
    fn the_types_panel_lists_a_struct_and_opens_its_fields(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        let loaded = with_struct();
        app.binary
            .update(cx, |binary, cx| binary.show_loaded(loaded.clone(), cx));
        cx.run_until_parked();
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
        let place = Types::place(&row("S")).unwrap();
        for _ in 0..2 {
            open_place(&workspace, &loaded, place.clone(), TabMode::Permanent, cx);
            cx.run_until_parked();
        }
        let tabs = workspace.read_with(cx, |workspace, cx| {
            workspace
                .active_pane()
                .read(cx)
                .items_of_type::<StructItem>()
                .count()
        });
        assert_eq!(tabs, 1);
        let item = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<StructItem>(cx)
            })
            .unwrap();
        let texts = item.read_with(cx, |item, _| item.texts());
        assert_eq!(
            texts,
            [
                "0x0000      4  a  u32",
                "0x0004      4  4 bytes not covered",
                "0x0008      4  b  u32",
                "0x000c      4  4 bytes not covered",
            ]
        );
    }
}
