//! The strings, imports and exports tables: their panels' rows, their columns, the engine
//! call each makes, and what Enter on a row shows: a string's or an import's references,
//! an export's function.

use borer_engine::analysis::render::{SlotUse, SymbolRow};
use borer_engine::num::from_usize;
use borer_engine::program::SymbolKind;
use borer_engine::strings::walk::StringLine;
use gpui::{Entity, SharedString};
use ui::IconName;
use workspace::Workspace;
use workspace::dock::DockPosition;

use crate::actions::{CycleSort, ToggleExports, ToggleImports, ToggleStrings};
use crate::app_assets::Glyph;
use crate::binary::Binary;
use crate::code_view::Role;
use crate::commands;
use crate::decompile_item::Form;
use crate::panels::PanelSpec;
use crate::places::Place;
use crate::rail::panel;
use crate::rows_panel::{Empty, Page, RowKind, RowsPanel, add, current, focus};
use crate::table::{Align, Column, Columns, Fit, Ink};
use crate::worker::{LoadedBinary, Referent, strings_blocking, symbols_blocking};

/// The strings table.
#[derive(Debug)]
pub enum Strings {}

/// The imports table.
#[derive(Debug)]
pub enum Imports {}

/// The exports table: exported symbols, then forwarded ones.
#[derive(Debug)]
pub enum Exports {}

/// Docks a side table may sit in.
const SIDE: &[DockPosition] = &[DockPosition::Right, DockPosition::Left];

/// Returns the panel row of the side table of kind `K`, first docked on the right.
///
/// # Arguments
///
/// * `key` - Its key and title.
/// * `icon` - Its icon.
/// * `toggle` - The action showing it.
const fn side<K: RowKind>(
    key: &'static str,
    icon: IconName,
    toggle: &'static dyn gpui::Action,
) -> PanelSpec {
    PanelSpec {
        key,
        title: key,
        icon: Glyph::Zed(icon),
        toggle,
        dock: DockPosition::Right,
        docks: SIDE,
        size_px: 480.0,
        hooks: panel::<RowsPanel<K>>(),
        add: add::<K>,
        remove: crate::panels::remove::<RowsPanel<K>>,
        focus: focus::<K>,
        current: current::<K>,
    }
}

/// Registers the tables' fallback on `workspace`, over the window's `binary`: Cycle Sort
/// with no table focused says to focus one.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let sort = binary.clone();
    commands::register(workspace, binary, move |_, _: &CycleSort, _, cx| {
        let why = "Cycle Sort sorts the focused table: focus a table first".to_owned();
        sort.update(cx, |binary, cx| binary.set_status(why, cx));
    });
}

/// The strings panel's row of [`crate::panels::PANELS`].
pub const STRINGS: PanelSpec = side::<Strings>("Strings", IconName::Quote, &ToggleStrings);

/// The imports panel's row of [`crate::panels::PANELS`].
pub const IMPORTS: PanelSpec = side::<Imports>("Imports", IconName::ArrowDownRight, &ToggleImports);

/// The exports panel's row of [`crate::panels::PANELS`].
pub const EXPORTS: PanelSpec = side::<Exports>("Exports", IconName::ArrowUpRight, &ToggleExports);

/// Every column of the strings table.
const STRING_COLUMNS: &[Column<StringLine>] = &[
    Column {
        header: "va",
        cell: |row| match row.va {
            Some(va) => format!("{va:#x}").into(),
            None => format!("off={:#x}", row.off).into(),
        },
        align: Align::Start,
        ink: Ink::Role(Role::Address),
        fit: Fit::Widest(|row| row.va.unwrap_or_else(|| row.off.saturating_mul(0x1_0000))),
        sort: Some(|a, b| (a.va, a.off).cmp(&(b.va, b.off))),
    },
    Column {
        header: "len",
        cell: |row| row.len.to_string().into(),
        align: Align::End,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| from_usize(row.len)),
        sort: Some(|a, b| a.len.cmp(&b.len)),
    },
    Column {
        header: "enc",
        cell: |row| row.encoding.name().into(),
        align: Align::Start,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| from_usize(row.encoding.name().len())),
        sort: Some(|a, b| a.encoding.name().cmp(b.encoding.name())),
    },
    Column {
        header: "text",
        cell: |row| row.text.clone().into(),
        align: Align::Start,
        ink: Ink::Role(Role::String),
        fit: Fit::Fill,
        sort: Some(|a, b| a.text.cmp(&b.text)),
    },
];

impl RowKind for Strings {
    type Row = StringLine;
    type Shown = Page<StringLine>;
    type Target = ();
    const PANEL: &'static PanelSpec = &STRINGS;
    const PLACEHOLDER: &'static str = "Filter strings";
    const TABLE: &'static str = "strings table";
    const FILTERING: &'static str = "Filtering strings";

    fn columns(_columns: Columns) -> &'static [Column<StringLine>] {
        STRING_COLUMNS
    }

    fn fetch(loaded: &LoadedBinary, (): &(), filter: &str, limit: usize) -> Page<StringLine> {
        let rows = strings_blocking(loaded, filter, limit);
        Page::counted(rows.rows, rows.total, "strings")
    }

    fn nothing(shown: &Page<StringLine>, query: &SharedString) -> Empty {
        shown.nothing("string", query)
    }

    fn place(row: &StringLine) -> Option<Place> {
        Self::referent(row).map(Place::Xrefs)
    }

    fn referent(row: &StringLine) -> Option<Referent> {
        row.va.map(Referent::Address)
    }
}

/// Returns the column of a symbol's address, headed `header`: hex, `-` for an import the
/// file gives no slot.
///
/// # Arguments
///
/// * `header` - The column's header.
const fn addr_column(header: &'static str) -> Column<SymbolRow> {
    Column {
        header,
        cell: |row| {
            row.addr
                .map_or_else(|| "-".into(), |va| format!("{va:#x}").into())
        },
        align: Align::Start,
        ink: Ink::Role(Role::Address),
        fit: Fit::Widest(|row| row.addr.unwrap_or(0)),
        sort: Some(|a, b| a.addr.cmp(&b.addr)),
    }
}

/// Returns the column of a symbol's name, in the color of `role`.
///
/// # Arguments
///
/// * `role` - What the names are.
const fn name_column(role: Role) -> Column<SymbolRow> {
    Column {
        header: "name",
        cell: |row| row.name.clone().into(),
        align: Align::Start,
        ink: Ink::Role(role),
        fit: Fit::Fill,
        sort: Some(|a, b| a.name.cmp(&b.name)),
    }
}

/// Returns what the `referenced` column says of an import's slot.
///
/// # Arguments
///
/// * `slot` - The engine's fact.
const fn slot_word(slot: SlotUse) -> &'static str {
    match slot {
        SlotUse::Referenced => "yes",
        SlotUse::Unreferenced => "no",
        SlotUse::NoSlot => "-",
    }
}

/// Returns a muted column of a symbol's text, headed `header`.
///
/// # Arguments
///
/// * `header` - The column's header.
/// * `cell` - The row's cell.
/// * `chars` - How wide the row's cell is.
/// * `sort` - Orders two rows by it.
const fn text_column(
    header: &'static str,
    cell: fn(&SymbolRow) -> SharedString,
    chars: fn(&SymbolRow) -> u64,
    sort: fn(&SymbolRow, &SymbolRow) -> std::cmp::Ordering,
) -> Column<SymbolRow> {
    Column {
        header,
        cell,
        align: Align::Start,
        ink: Ink::Muted,
        fit: Fit::Widest(chars),
        sort: Some(sort),
    }
}

/// Every column of the imports table.
const IMPORT_COLUMNS: &[Column<SymbolRow>] = &[
    addr_column("slot"),
    text_column(
        "module",
        |row| row.module.clone().unwrap_or_default().into(),
        |row| {
            row.module
                .as_ref()
                .map_or(0, |m| from_usize(m.chars().count()))
        },
        |a, b| a.module.cmp(&b.module),
    ),
    name_column(Role::Import),
    text_column(
        "referenced",
        |row| slot_word(row.slot).into(),
        |row| from_usize(slot_word(row.slot).len()),
        |a, b| slot_word(a.slot).cmp(slot_word(b.slot)),
    ),
];

/// Every column of the exports table.
const EXPORT_COLUMNS: &[Column<SymbolRow>] = &[
    addr_column("addr"),
    name_column(Role::Function),
    text_column(
        "forward",
        |row| row.forward.clone().unwrap_or_default().into(),
        |row| {
            row.forward
                .as_ref()
                .map_or(0, |f| from_usize(f.chars().count()))
        },
        |a, b| a.forward.cmp(&b.forward),
    ),
];

impl RowKind for Imports {
    type Row = SymbolRow;
    type Shown = Page<SymbolRow>;
    type Target = ();
    const PANEL: &'static PanelSpec = &IMPORTS;
    const PLACEHOLDER: &'static str = "Filter imports";
    const TABLE: &'static str = "imports table";
    const FILTERING: &'static str = "Filtering imports";

    fn columns(_columns: Columns) -> &'static [Column<SymbolRow>] {
        IMPORT_COLUMNS
    }

    fn fetch(loaded: &LoadedBinary, (): &(), filter: &str, limit: usize) -> Page<SymbolRow> {
        let rows = symbols_blocking(loaded, SymbolKind::Import, filter, limit);
        Page::counted(rows.rows, rows.total, "imports")
    }

    fn nothing(shown: &Page<SymbolRow>, query: &SharedString) -> Empty {
        shown.nothing("import", query)
    }

    fn place(row: &SymbolRow) -> Option<Place> {
        Self::referent(row).map(Place::Xrefs)
    }

    fn referent(row: &SymbolRow) -> Option<Referent> {
        row.addr.map(Referent::Import)
    }
}

impl RowKind for Exports {
    type Row = SymbolRow;
    type Shown = Page<SymbolRow>;
    type Target = ();
    const PANEL: &'static PanelSpec = &EXPORTS;
    const PLACEHOLDER: &'static str = "Filter exports";
    const TABLE: &'static str = "exports table";
    const FILTERING: &'static str = "Filtering exports";

    fn columns(_columns: Columns) -> &'static [Column<SymbolRow>] {
        EXPORT_COLUMNS
    }

    fn fetch(loaded: &LoadedBinary, (): &(), filter: &str, limit: usize) -> Page<SymbolRow> {
        let exports = symbols_blocking(loaded, SymbolKind::Export, filter, limit);
        let left = limit.saturating_sub(exports.rows.len());
        let forwards = symbols_blocking(loaded, SymbolKind::Forwarder, filter, left);
        let one = Page::counted(exports.rows, exports.total, "exports");
        let two = Page::counted(forwards.rows, forwards.total, "forwarders");
        let header = match two.total {
            0 => one.header.to_string(),
            _ => format!("{}, {}", one.header, two.header),
        };
        let mut rows = one.rows;
        rows.extend(two.rows);
        Page {
            header: header.into(),
            total: one.total.saturating_add(two.total),
            rows,
        }
    }

    fn nothing(shown: &Page<SymbolRow>, query: &SharedString) -> Empty {
        shown.nothing("export", query)
    }

    fn place(row: &SymbolRow) -> Option<Place> {
        match (row.addr, &row.forward) {
            (Some(entry), None) => Some(Place::Code {
                entry,
                form: Form::Decompile,
                at: None,
            }),
            (Some(_) | None, _) => None,
        }
    }

    fn referent(row: &SymbolRow) -> Option<Referent> {
        row.addr.map(Referent::Address)
    }
}
