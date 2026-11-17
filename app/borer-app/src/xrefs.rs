//! The xrefs panel: the engine's cross-reference rows of one referent, in Zed's bottom dock.
//!
//! One row per function making them, under the engine's own header. Enter opens a row's
//! listing at its first site, or a pointer stored in data in the hex tab.

use borer_engine::analysis::render::{XrefRow, XrefRows};
use borer_engine::num::from_usize;
use gpui::{Context, SharedString, Window};
use ui::IconName;
use workspace::Workspace;
use workspace::dock::DockPosition;

use crate::actions::ToggleXrefs;
use crate::app_assets::Glyph;
use crate::code_view::Role;
use crate::decompile_item::Form;
use crate::panels::PanelSpec;
use crate::places::Place;
use crate::rows_panel::{Empty, Page, RowKind, RowsPanel, add, focus};
use crate::table::{Align, Column, Columns, Fit, Ink};
use crate::worker::{LoadedBinary, Referent, xrefs_blocking};

/// The cross-reference table.
#[derive(Debug)]
pub enum Xrefs {}

/// The xrefs panel.
pub type XrefsPanel = RowsPanel<Xrefs>;

/// The xrefs panel's row of [`crate::panels::PANELS`].
pub const XREFS: PanelSpec = PanelSpec {
    key: "Xrefs",
    title: "Xrefs",
    icon: Glyph::Zed(IconName::ArrowRightLeft),
    toggle: &ToggleXrefs,
    dock: DockPosition::Bottom,
    docks: &[
        DockPosition::Bottom,
        DockPosition::Left,
        DockPosition::Right,
    ],
    size_px: 260.0,
    hooks: crate::rail::panel::<XrefsPanel>(),
    add: add::<Xrefs>,
    remove: crate::panels::remove::<XrefsPanel>,
    focus: focus::<Xrefs>,
};

/// Most sites a row's `sites` cell names before it counts the rest.
const SITES_SHOWN: usize = 8;

/// Returns a row's sites as its cell: each site and what it does, the first
/// [`SITES_SHOWN`], then how many more.
///
/// # Arguments
///
/// * `row` - The engine's row.
fn sites_cell(row: &XrefRow) -> SharedString {
    let mut cell: Vec<String> = row
        .sites
        .iter()
        .take(SITES_SHOWN)
        .map(|(va, kind)| format!("{va:#x} {}", kind.word()))
        .collect();
    if let Some(more) = row.sites.len().checked_sub(SITES_SHOWN).filter(|&n| n > 0) {
        cell.push(format!("+{more} more"));
    }
    cell.join(", ").into()
}

/// Every column of the cross-reference table; `own refs` counts the sites of the row's own
/// function, not those of the functions running the same code.
const XREF_COLUMNS: &[Column<XrefRow>] = &[
    Column {
        header: "entry",
        cell: |row| {
            row.entry
                .map_or_else(|| "-".into(), |va| format!("{va:#x}").into())
        },
        align: Align::Start,
        ink: Ink::Role(Role::Address),
        fit: Fit::Widest(|row| row.entry.unwrap_or(0)),
        sort: Some(|a, b| a.entry.cmp(&b.entry)),
    },
    Column {
        header: "function",
        cell: |row| row.name.clone().into(),
        align: Align::Start,
        ink: Ink::Role(Role::Function),
        fit: Fit::Widest(|row| from_usize(row.name.chars().count())),
        sort: Some(|a, b| a.name.cmp(&b.name)),
    },
    Column {
        header: "own refs",
        cell: |row| row.sites.len().to_string().into(),
        align: Align::End,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| from_usize(row.sites.len())),
        sort: Some(|a, b| a.sites.len().cmp(&b.sites.len())),
    },
    Column {
        header: "same code",
        cell: |row| row.folded.len().to_string().into(),
        align: Align::End,
        ink: Ink::Muted,
        fit: Fit::Widest(|row| from_usize(row.folded.len())),
        sort: Some(|a, b| a.folded.len().cmp(&b.folded.len())),
    },
    Column {
        header: "sites",
        cell: sites_cell,
        align: Align::Start,
        ink: Ink::Role(Role::Address),
        fit: Fit::Fill,
        sort: None,
    },
];

/// What the xrefs panel says before anything is chosen.
pub const NOTHING_CHOSEN: &str =
    "Nothing chosen: run Xrefs on a table row, a code tab or the hex tab, or Go to an address";

/// Returns the panel's page of the engine's listing.
///
/// Its header is the one the engine spells for it ([`XrefRows::spell`]): the sites and
/// their targets, how many groups show of how many, a cap the sites hit and the notes.
///
/// # Arguments
///
/// * `rows` - The engine's listing.
fn xrefs_page(rows: XrefRows) -> Page<XrefRow> {
    let spelled = rows.spell();
    let header: Vec<&str> = spelled
        .lines()
        .take_while(|line| !line.starts_with("# function:"))
        .map(|line| line.trim_start_matches('#').trim())
        .filter(|line| !line.is_empty())
        .collect();
    Page {
        header: header.join("; ").into(),
        total: rows.groups,
        rows: rows.rows,
    }
}

impl RowKind for Xrefs {
    type Row = XrefRow;
    type Shown = Page<XrefRow>;
    type Target = Option<Referent>;
    const PANEL: &'static PanelSpec = &XREFS;
    const PLACEHOLDER: &'static str = "";
    const TABLE: &'static str = "xrefs table";
    const FILTERING: &'static str = "Listing xrefs";
    const FILTERS: bool = false;

    fn columns(_columns: Columns) -> &'static [Column<XrefRow>] {
        XREF_COLUMNS
    }

    fn fetch(
        loaded: &LoadedBinary,
        target: &Option<Referent>,
        _filter: &str,
        limit: usize,
    ) -> Page<XrefRow> {
        match target {
            Some(referent) => xrefs_page(xrefs_blocking(loaded, *referent, limit)),
            None => Page {
                header: NOTHING_CHOSEN.into(),
                total: 0,
                rows: Vec::new(),
            },
        }
    }

    fn nothing(shown: &Page<XrefRow>, _query: &SharedString) -> Empty {
        Empty::Nothing(shown.header.clone())
    }

    fn place(row: &XrefRow) -> Option<Place> {
        let site = row.sites.first().map(|(va, _)| *va);
        Some(match row.entry {
            Some(entry) => Place::Code {
                entry,
                form: Form::Listing,
                at: site,
            },
            None => Place::Hex { at: site },
        })
    }

    fn referent(row: &XrefRow) -> Option<Referent> {
        row.entry.map(Referent::Address)
    }
}

/// Focuses the xrefs panel on the references to `referent`.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `referent` - What the references are to.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn show_xrefs(
    workspace: &mut Workspace,
    referent: Referent,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    if let Some(panel) = workspace.focus_panel::<XrefsPanel>(window, cx) {
        panel.update(cx, |panel, cx| panel.set_target(Some(referent), cx));
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::render::{
        SlotUse, SymbolRow, XREF_ROWS_MAX, XrefRow, XrefView, xref_rows, xref_rows_of_import,
    };
    use borer_engine::analysis::{Analysis, EnumSource, Overlay, RefKind};
    use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
    use borer_engine::strings::Encoding;
    use borer_engine::strings::walk::StringLine;
    use gpui::{Entity, Focusable as _, TestAppContext, VisualTestContext};
    use picker::Picker;

    use super::{NOTHING_CHOSEN, Xrefs, XrefsPanel};
    use crate::actions::Xrefs as XrefsAction;
    use crate::app_view::tests::{CALLEE, CALLER, init, loaded_of, open, open_place};
    use crate::decompile_item::{DecompileItem, Form, TabMode};
    use crate::goto::GoToDelegate;
    use crate::hex_item::HexItem;
    use crate::places::Place;
    use crate::rows_panel::RowKind;
    use crate::rows_panel::tests::{panel_of, sample};
    use crate::tables::{Exports, Imports, Strings};
    use crate::worker::{LoadedBinary, Referent};

    /// One page of every group.
    const PAGE: XrefView = XrefView::Page {
        offset: 0,
        limit: XREF_ROWS_MAX,
    };

    /// Returns the xrefs panel's target.
    fn target(panel: &Entity<XrefsPanel>, cx: &mut VisualTestContext) -> Option<Referent> {
        panel.read_with(cx, |panel, _| *panel.target())
    }

    /// Each row names the place Enter opens, without a window.
    ///
    /// A string and an import their xrefs, an export its function and a forwarder nothing,
    /// an xref row its listing at the first site, or the hex tab for a pointer in data.
    #[test]
    fn each_row_names_its_place() {
        let string = StringLine {
            off: 0x100,
            va: Some(0x1100),
            len: 5,
            encoding: Encoding::Ascii,
            text: "hello".to_owned(),
        };
        let address = Referent::Address(0x1100);
        assert_eq!(Strings::place(&string), Some(Place::Xrefs(address)));
        let symbol = |kind, forward: Option<&str>| SymbolRow {
            kind,
            addr: Some(0x2000),
            name: "f".to_owned(),
            module: None,
            slot: SlotUse::Referenced,
            forward: forward.map(str::to_owned),
        };
        let import = symbol(SymbolKind::Import, None);
        let slot = Place::Xrefs(Referent::Import(0x2000));
        assert_eq!(Imports::place(&import), Some(slot));
        let code = |entry, form, at| Place::Code { entry, form, at };
        let export = symbol(SymbolKind::Export, None);
        let decompile = code(0x2000, Form::Decompile, None);
        assert_eq!(Exports::place(&export), Some(decompile));
        assert_eq!(
            Exports::place(&symbol(SymbolKind::Forwarder, Some("x"))),
            None
        );
        let row = |entry| XrefRow {
            entry,
            name: "f".to_owned(),
            sites: vec![(0x1008, RefKind::Call)],
            folded: Vec::new(),
        };
        let listing = code(CALLER, Form::Listing, Some(0x1008));
        assert_eq!(Xrefs::place(&row(Some(CALLER))), Some(listing));
        let data = Place::Hex { at: Some(0x1008) };
        assert_eq!(Xrefs::place(&row(None)), Some(data));
    }

    /// Xrefs is answered by whatever holds the focus: a table's row lists its referent, a
    /// code tab its function, the hex tab its cursor; with nothing that names an address
    /// focused, Go to opens to ask for one.
    #[gpui::test]
    fn xrefs_answers_from_whatever_holds_the_focus(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let xrefs = panel_of::<Xrefs>(&workspace, &loaded, cx);
        assert_eq!(target(&xrefs, cx), None);
        let ask = |cx: &mut VisualTestContext| {
            cx.dispatch_action(XrefsAction);
            cx.run_until_parked();
        };
        panel_of::<Strings>(&workspace, &loaded, cx);
        ask(cx);
        assert_eq!(target(&xrefs, cx), Some(Referent::Address(0x1100)));
        let callee = Place::Code {
            entry: CALLEE,
            form: Form::Decompile,
            at: None,
        };
        open_place(&workspace, &loaded, callee, TabMode::Permanent, cx);
        cx.run_until_parked();
        ask(cx);
        assert_eq!(target(&xrefs, cx), Some(Referent::Address(CALLEE)));
        let hex = Place::Hex { at: Some(0x1104) };
        open_place(&workspace, &loaded, hex, TabMode::Permanent, cx);
        cx.run_until_parked();
        ask(cx);
        assert_eq!(target(&xrefs, cx), Some(Referent::Address(0x1104)));
        workspace.update_in(cx, |workspace, window, cx| {
            let pane = workspace.active_pane().clone();
            pane.update(cx, |pane, cx| {
                pane.close_all_items(&workspace::CloseAllItems::default(), window, cx)
            })
            .detach();
        });
        cx.run_until_parked();
        let pane = workspace.read_with(cx, |workspace, _| workspace.active_pane().clone());
        cx.update(|window, cx| window.focus(&pane.focus_handle(cx), cx));
        ask(cx);
        let asked = workspace.read_with(cx, |workspace, cx| {
            workspace.active_modal::<Picker<GoToDelegate>>(cx).is_some()
        });
        assert!(asked);
    }

    /// Xrefs on the callee's tab lists the engine's rows of its references, the caller's
    /// two call sites, and Enter on the caller's row opens the caller's listing at its first
    /// call.
    #[gpui::test]
    fn xrefs_of_a_callee_list_its_call_sites_and_enter_opens_the_caller(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let panel = panel_of::<Xrefs>(&workspace, &loaded, cx);
        let header = panel.read_with(cx, |panel, _| panel.rows().unwrap().header.clone());
        assert_eq!(header, NOTHING_CHOSEN);
        let callee = Place::Code {
            entry: CALLEE,
            form: Form::Decompile,
            at: None,
        };
        open_place(&workspace, &loaded, callee, TabMode::Permanent, cx);
        cx.run_until_parked();
        cx.dispatch_action(XrefsAction);
        cx.run_until_parked();
        let (p, a, o) = (&loaded.program, &loaded.analysis, &loaded.overlay);
        let want = xref_rows(p, a, o, CALLEE, PAGE);
        panel.read_with(cx, |panel, _| {
            let shown = panel.rows().unwrap();
            assert_eq!(shown.rows, want.rows);
            assert_eq!(shown.total, want.groups);
            let spelled = want.spell();
            let first = spelled.lines().next().unwrap().trim_start_matches("# ");
            assert!(shown.header.starts_with(first), "{}", shown.header);
            let sites: Vec<u64> = shown.rows[0].sites.iter().map(|(va, _)| *va).collect();
            assert_eq!(sites, [0x1008, 0x1016]);
        });
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        let opened = workspace.read_with(cx, |workspace, cx| {
            let item = workspace.active_item_as::<DecompileItem>(cx)?;
            let item = item.read(cx);
            Some((item.entry()?, item.form()))
        });
        assert_eq!(opened, Some((CALLER, Form::Listing)));
    }

    /// Returns a PE whose code calls `Sleep` once through its import slot and once through
    /// a thunk jumping through that slot.
    fn imported() -> Arc<LoadedBinary> {
        let mut bytes = vec![0xccu8; 0x200];
        // ASM: call 0x1020 ; call qword ptr [rip+0xff5] ; ret
        let code: &[u8] = &[
            0xe8, 0x1b, 0x00, 0x00, 0x00, 0xff, 0x15, 0xf5, 0x0f, 0x00, 0x00, 0xc3,
        ];
        // ASM: jmp qword ptr [rip+0xfda]
        let thunk: &[u8] = &[0xff, 0x25, 0xda, 0x0f, 0x00, 0x00];
        bytes[..code.len()].copy_from_slice(code);
        bytes[0x20..0x20 + thunk.len()].copy_from_slice(thunk);
        bytes[0x100..0x108].fill(0);
        let sections = vec![
            Section::mapped(".text", 0x1000, 0, 0x100, false, true),
            Section::mapped(".idata", 0x2000, 0x100, 0x100, false, false),
        ];
        let mut program = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), sections);
        program.format = BinaryFormat::Pe;
        program.symbols = vec![Symbol {
            name: "KERNEL32.dll!Sleep".to_owned(),
            addr: 0x2000,
            kind: SymbolKind::Import,
        }];
        let analysis = Analysis::compute(&program);
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        loaded_of(program, analysis, overlay)
    }

    /// Enter on an import's row gathers the references to its slot and to the thunk
    /// jumping through it, as the engine gathers an import's; a new binary clears it.
    #[gpui::test]
    fn xrefs_of_an_import_gather_its_slot_and_thunk(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = imported();
        let xrefs = panel_of::<Xrefs>(&workspace, &loaded, cx);
        panel_of::<Imports>(&workspace, &loaded, cx);
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        let (p, a, o) = (&loaded.program, &loaded.analysis, &loaded.overlay);
        let want = xref_rows_of_import(p, a, o, 0x2000, PAGE).unwrap();
        assert!(want.targets.contains(&0x1020), "{:?}", want.targets);
        assert_eq!(target(&xrefs, cx), Some(Referent::Import(0x2000)));
        xrefs.read_with(cx, |panel, _| {
            let shown = panel.rows().unwrap();
            assert_eq!(shown.rows, want.rows);
            let sites: Vec<u64> = shown
                .rows
                .iter()
                .flat_map(|row| row.sites.iter().map(|(va, _)| *va))
                .collect();
            for site in [0x1000, 0x1005] {
                assert!(sites.contains(&site), "{sites:x?}");
            }
        });
        panel_of::<Xrefs>(&workspace, &sample(), cx);
        assert_eq!(target(&xrefs, cx), None);
        let hex = workspace.read_with(cx, |workspace, cx| {
            workspace.items_of_type::<HexItem>(cx).count()
        });
        assert_eq!(hex, 0);
    }
}
