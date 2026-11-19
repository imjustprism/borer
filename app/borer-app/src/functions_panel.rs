//! The functions panel: the open binary's function table as a rows panel of Zed's left
//! dock, a row opening its function's decompile view.

use std::sync::Arc;

use borer_engine::analysis::render::{
    FunctionOrder, FunctionRow, FunctionRows, INCOMPLETE_NOTE, LeftOut,
};
use borer_engine::view::Ref;
use gpui::{Entity, SharedString};
use ui::IconName;
use workspace::Workspace;
use workspace::dock::DockPosition;

use crate::actions::{FocusFilter, ToggleFunctionColumns, ToggleFunctions};
use crate::app_assets::Glyph;
use crate::binary::Binary;
use crate::commands;
use crate::function_columns::{Column, Columns};
use crate::panels::{PanelSpec, remove};
use crate::places::Place;
use crate::rail::panel;
pub use crate::rows_panel::Empty;
use crate::rows_panel::{Answer, RowKind, RowsPanel, add, current, focus};
use crate::table::{count_text, grouped};
use crate::worker::{LoadedBinary, filter_rows_blocking};

/// The functions panel's row of [`crate::panels::PANELS`].
pub const PANEL: PanelSpec = PanelSpec {
    key: "Functions",
    title: "Functions",
    icon: Glyph::Zed(IconName::ListTree),
    toggle: &ToggleFunctions,
    dock: DockPosition::Left,
    docks: &[DockPosition::Left, DockPosition::Right],
    size_px: 560.0,
    hooks: panel::<FunctionsPanel>(),
    add: add::<Functions>,
    remove: remove::<FunctionsPanel>,
    focus: focus::<Functions>,
    current: current::<Functions>,
};

/// Registers the functions panel's actions on `workspace`: focus its filter, and show or
/// hide its extra columns; [`crate::panels::register_toggles`] shows or focuses it.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    commands::register(
        workspace,
        binary,
        |workspace, _: &FocusFilter, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        },
    );
    commands::register(
        workspace,
        binary,
        |workspace, _: &ToggleFunctionColumns, _, cx| {
            if let Some(panel) = workspace.panel::<FunctionsPanel>(cx) {
                panel.update(cx, FunctionsPanel::toggle_columns);
            }
        },
    );
}

/// Returns what the engine left out of the function table, as a person reads it.
///
/// A short `42 hidden`, and a sentence naming the parts and the filter words that list
/// them.
///
/// # Returns
///
/// `None` when nothing was left out.
///
/// # Arguments
///
/// * `left_out` - The import thunks and exception funclets the engine left out.
#[must_use]
pub fn hidden(left_out: LeftOut) -> Option<(SharedString, SharedString)> {
    let parts: Vec<(usize, &str, &str)> = [
        (left_out.thunks, "import thunks", "thunk"),
        (left_out.funclets, "exception funclets", "funclet"),
    ]
    .into_iter()
    .filter(|(count, _, _)| *count > 0)
    .collect();
    if parts.is_empty() {
        return None;
    }
    let all = left_out.thunks.saturating_add(left_out.funclets);
    let named: Vec<String> = parts
        .iter()
        .map(|(count, plural, _)| count_text(*count, *count, plural))
        .collect();
    let words: Vec<String> = parts
        .iter()
        .map(|(_, _, word)| format!("\"{word}\""))
        .collect();
    let tip = format!(
        "Hidden: {}. Type {} in the filter to list them.",
        named.join(" and "),
        words.join(" or ")
    );
    Some((format!("{} hidden", grouped(all)).into(), tip.into()))
}

/// Returns the open binary's count of functions for the status line: `481 functions`,
/// then `, 42 hidden` when the engine left some out.
///
/// # Arguments
///
/// * `rows` - The engine's unfiltered function table.
#[must_use]
pub fn function_count(rows: &FunctionRows) -> String {
    let count = count_text(rows.total, rows.total, rows.noun);
    match hidden(rows.left_out) {
        Some((short, _)) => format!("{count}, {short}"),
        None => count,
    }
}

/// The open binary's function table, in a dock.
pub type FunctionsPanel = RowsPanel<Functions>;

/// The engine's functions, as rows of a panel.
#[derive(Debug)]
pub struct Functions;

impl RowKind for Functions {
    type Row = FunctionRow;
    type Shown = FunctionRows;
    type Target = ();
    const PANEL: &'static PanelSpec = &PANEL;
    const PLACEHOLDER: &'static str = "Filter by name or address";
    const TABLE: &'static str = "function table";
    const FILTERING: &'static str = "Filtering functions";
    const PREVIEWS: bool = true;

    fn columns(columns: Columns) -> &'static [Column] {
        columns.shown()
    }

    fn warning(shown: &FunctionRows) -> Option<&'static str> {
        shown
            .incomplete
            .then(|| INCOMPLETE_NOTE.trim_start_matches("# "))
    }

    fn first(loaded: &LoadedBinary) -> Option<Arc<FunctionRows>> {
        Some(loaded.initial_rows.clone())
    }

    fn fetch(loaded: &LoadedBinary, (): &(), filter: &str, limit: usize) -> FunctionRows {
        filter_rows_blocking(loaded, filter, FunctionOrder::Address, limit)
    }

    fn nothing(shown: &FunctionRows, query: &SharedString) -> Empty {
        if query.is_empty() {
            Empty::NoFunction(shown.left_out)
        } else {
            Empty::NoMatch(query.clone())
        }
    }

    fn place(row: &FunctionRow) -> Option<Place> {
        Some(Place::decompile(row.entry))
    }

    fn subject(row: &FunctionRow) -> Option<Ref> {
        Some(Ref::Function(row.entry))
    }
}

impl Answer<FunctionRow> for FunctionRows {
    fn rows(&self) -> &[FunctionRow] {
        &self.rows
    }

    fn rows_mut(&mut self) -> &mut [FunctionRow] {
        &mut self.rows
    }

    fn total(&self) -> usize {
        self.total
    }

    fn showing(&self) -> SharedString {
        count_text(self.rows.len(), self.total, self.noun).into()
    }

    fn hidden(&self) -> Option<(SharedString, SharedString)> {
        hidden(self.left_out)
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    use borer_engine::analysis::render::{
        FunctionOrder, FunctionRow, FunctionRows, LeftOut, RowSource,
    };
    use gpui::{Entity, SharedString, TestAppContext, VisualTestContext, px};
    use workspace::dock::DockPosition;
    use workspace::{AppState, Workspace};

    use super::{Empty, Functions, FunctionsPanel, function_count, hidden};
    use crate::actions::FocusFilter;
    use crate::app_view::add_functions_panel;
    use crate::app_view::tests::{CALLEE, CALLER, init, open, sample, shown};
    use crate::binary::BinaryEvent;
    use crate::card::CARD_SELECTOR;
    use crate::decompile_item::Form;
    use crate::places::Place;
    use crate::rows_panel::Answer;
    use crate::rows_panel::RowKind as _;
    use crate::rows_panel::{ENTRY_SELECTOR, HEADER_SELECTOR, ROW_SELECTOR};
    use crate::worker::Jobs;

    /// The count line says how many functions show and, apart, how many are hidden.
    ///
    /// The hidden count's tooltip names the import thunks and exception funclets and the
    /// filter words that list them; nothing is hidden when nothing was left out.
    ///
    /// # Panics
    ///
    /// Panics if a count or the tooltip says anything else.
    #[test]
    fn the_count_line_says_what_is_hidden_in_a_persons_words() {
        let rows = FunctionRows {
            total: 481,
            noun: "functions",
            order: FunctionOrder::Address,
            left_out: LeftOut {
                thunks: 39,
                funclets: 3,
            },
            incomplete: false,
            rows: Vec::new(),
        };
        assert_eq!(Answer::<FunctionRow>::showing(&rows), "0 of 481 functions");
        let tip = concat!(
            "Hidden: 39 import thunks and 3 exception funclets. ",
            "Type \"thunk\" or \"funclet\" in the filter to list them."
        );
        assert_eq!(
            rows.hidden(),
            Some((SharedString::from("42 hidden"), SharedString::from(tip)))
        );
        assert_eq!(function_count(&rows), "481 functions, 42 hidden");
        let one = LeftOut {
            thunks: 0,
            funclets: 1,
        };
        let tip = "Hidden: 1 exception funclet. Type \"funclet\" in the filter to list them.";
        assert_eq!(
            hidden(one),
            Some((SharedString::from("1 hidden"), SharedString::from(tip)))
        );
        assert_eq!(hidden(LeftOut::default()), None);
    }

    /// Vertical padding of a cell of Zed's table at the pin, both sides together, in rems
    /// (`py_0p5` in `data_table.rs`).
    const CELL_PAD_Y_REMS: f32 = 0.25;

    /// Opens a window over the app's workspace with a functions panel docked on the left
    /// before any load, and returns the workspace.
    fn open_docked<'a>(
        app_state: &Arc<AppState>,
        cx: &'a mut TestAppContext,
    ) -> (Entity<Workspace>, &'a mut VisualTestContext) {
        let (app, cx) = open(app_state, cx);
        cx.update(|window, cx| {
            add_functions_panel(&app.workspace, &app.binary, DockPosition::Left, window, cx);
        });
        (app.workspace, cx)
    }

    /// Returns `workspace`'s functions panel showing every row of the sample binary.
    fn showing_sample(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Entity<FunctionsPanel> {
        let panel = panel_of(workspace, cx);
        let loaded = sample();
        panel.update_in(cx, |panel, window, cx| {
            panel.show(loaded.clone(), loaded.initial_rows.clone(), window, cx);
        });
        panel
    }

    /// Settles the work in flight and lays the window out twice, the second time at the
    /// table width the first measured.
    fn draw(cx: &mut VisualTestContext) {
        for _ in 0..2 {
            cx.run_until_parked();
            cx.update(|window, cx| window.draw(cx).clear(cx));
        }
    }

    /// Returns `workspace`'s functions panel.
    ///
    /// # Panics
    ///
    /// Panics if the workspace has none.
    fn panel_of(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Entity<FunctionsPanel> {
        workspace
            .read_with(cx, |workspace, cx| workspace.panel::<FunctionsPanel>(cx))
            .unwrap()
    }

    /// Shows `rows` of the sample binary in `workspace`'s functions panel and lays it out.
    fn show_rows(workspace: &Entity<Workspace>, rows: FunctionRows, cx: &mut VisualTestContext) {
        let panel = panel_of(workspace, cx);
        panel.update_in(cx, |panel, window, cx| {
            panel.show(sample(), Arc::new(rows), window, cx);
        });
        draw(cx);
    }

    /// Returns hand-built rows of functions at `entries`, each one byte long.
    fn rows_at(entries: &[u64]) -> FunctionRows {
        let row = |&entry: &u64| FunctionRow {
            entry,
            size: 1,
            blocks: 1,
            instrs: 1,
            callers: 0,
            callees: 0,
            src: RowSource::User,
            name: format!("f{entry:x}"),
        };
        FunctionRows {
            total: entries.len(),
            noun: "functions",
            order: FunctionOrder::Address,
            left_out: LeftOut::default(),
            incomplete: false,
            rows: entries.iter().map(row).collect(),
        }
    }

    /// The function table draws no border under its rows: a row is as tall as its cells'
    /// content and Zed's cell padding, not a pixel more.
    ///
    /// # Panics
    ///
    /// Panics if a row is taller, or no row is laid out.
    #[gpui::test]
    fn the_function_table_draws_no_row_border(cx: &mut TestAppContext) {
        the_function_table_draws_no_row_border_steps(cx);
    }

    /// Runs the steps of [`the_function_table_draws_no_row_border`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_function_table_draws_no_row_border`] says.
    fn the_function_table_draws_no_row_border_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        show_rows(&workspace, rows_at(&[0x1000, 0x2000, 0x3000]), cx);
        let row = cx.debug_bounds(ROW_SELECTOR).unwrap();
        let entry = cx.debug_bounds(ENTRY_SELECTOR).unwrap();
        let pad = cx.update(|window, _| window.rem_size()) * CELL_PAD_Y_REMS;
        let extra = row.size.height - entry.size.height - pad;
        assert!(
            extra.abs() < px(0.5),
            "a row is {extra:?} taller than its cells"
        );
    }

    /// Before a load the panel has no rows and offers to open a binary; while a load reads
    /// a file it names the file; when the load fails it gives the binary's reason and
    /// offers to open another.
    ///
    /// # Panics
    ///
    /// Panics if a step says anything else.
    #[gpui::test]
    fn the_panel_follows_a_failing_load(cx: &mut TestAppContext) {
        the_panel_follows_a_failing_load_steps(cx);
    }

    /// Runs the steps of [`the_panel_follows_a_failing_load`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_panel_follows_a_failing_load`] says.
    fn the_panel_follows_a_failing_load_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        let panel = panel_of(&workspace, cx);
        let empty = |cx: &mut VisualTestContext| panel.read_with(cx, |panel, cx| panel.empty(cx));
        assert_eq!(empty(cx), Some(Empty::NoBinary));
        assert!(Empty::NoBinary.offers_open());
        let path = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        let binary = panel.read_with(cx, |panel, _| panel.binary().clone());
        binary.update(cx, |binary, cx| binary.open_path(path.clone(), cx));
        let reading = empty(cx);
        assert_eq!(reading, Some(Empty::Reading(path)));
        assert_eq!(
            reading.map(|empty| empty.says()),
            Some("Reading borer-app-no-such-binary.exe".into())
        );
        cx.run_until_parked();
        let reason = binary.read_with(cx, |binary, _| binary.load_error().map(str::to_owned));
        let failed = empty(cx).unwrap();
        assert_eq!(failed, Empty::LoadFailed(reason.unwrap()));
        assert!(failed.offers_open());
        assert!(failed.says().starts_with("Load failed: "));
    }

    /// A binary whose functions the engine all left out says so in the engine's words, how
    /// many and how to list them, and the count line is the engine's own.
    ///
    /// # Panics
    ///
    /// Panics if the panel words it otherwise.
    #[gpui::test]
    fn no_function_names_what_the_engine_left_out(cx: &mut TestAppContext) {
        no_function_names_what_the_engine_left_out_steps(cx);
    }

    /// Runs the steps of [`no_function_names_what_the_engine_left_out`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`no_function_names_what_the_engine_left_out`] says.
    fn no_function_names_what_the_engine_left_out_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        let left_out = LeftOut {
            thunks: 3,
            funclets: 0,
        };
        show_rows(
            &workspace,
            FunctionRows {
                left_out,
                ..rows_at(&[])
            },
            cx,
        );
        let panel = panel_of(&workspace, cx);
        let (empty, showing) = panel.read_with(cx, |panel, cx| {
            (
                panel.empty(cx),
                panel
                    .rows()
                    .map(|rows| Answer::<FunctionRow>::showing(&**rows)),
            )
        });
        let empty = empty.unwrap();
        assert_eq!(empty, Empty::NoFunction(left_out));
        assert!(!empty.offers_open());
        let note = "Hidden: 3 import thunks. Type \"thunk\" in the filter to list them.";
        assert_eq!(
            empty.says(),
            SharedString::from(format!("The engine found no function. {note}"))
        );
        assert_eq!(showing, Some(SharedString::from("0 functions")));
    }

    /// A filter nothing matches is quoted as the query that selected the rows shown, and a
    /// newer query whose answer is not in yet does not change what the panel says.
    ///
    /// # Panics
    ///
    /// Panics if the panel quotes another query.
    #[gpui::test]
    fn no_match_quotes_the_query_of_the_rows_shown(cx: &mut TestAppContext) {
        no_match_quotes_the_query_of_the_rows_shown_steps(cx);
    }

    /// Runs the steps of [`no_match_quotes_the_query_of_the_rows_shown`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`no_match_quotes_the_query_of_the_rows_shown`] says.
    fn no_match_quotes_the_query_of_the_rows_shown_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        let panel = panel_of(&workspace, cx);
        let set_filter = |text: &'static str, cx: &mut VisualTestContext| {
            panel.update_in(cx, |panel, window, cx| {
                panel
                    .filter
                    .update(cx, |editor, cx| editor.set_text(text, window, cx));
            });
        };
        let loaded = sample();
        panel.update_in(cx, |panel, window, cx| {
            panel.show(loaded.clone(), loaded.initial_rows.clone(), window, cx);
        });
        set_filter("zz", cx);
        draw(cx);
        let zz = Some(Empty::NoMatch("zz".into()));
        let empty = |cx: &mut VisualTestContext| panel.read_with(cx, |panel, cx| panel.empty(cx));
        assert_eq!(empty(cx), zz);
        assert_eq!(
            zz.map(|empty| empty.says()),
            Some("No function matches \"zz\"".into())
        );
        set_filter("zzz", cx);
        assert_eq!(empty(cx), Some(Empty::NoMatch("zz".into())));
        draw(cx);
        assert_eq!(empty(cx), Some(Empty::NoMatch("zzz".into())));
    }

    /// A binary that starts loading while a filter runs stops the filter: no rows stay, the
    /// load's failure is what the panel says, and the filter's ticket is settled; the load is
    /// listed by the words the panel reads it with.
    ///
    /// # Panics
    ///
    /// Panics if the stopped filter's rows come back, or its ticket stays open.
    #[gpui::test]
    fn a_load_stops_a_running_filter(cx: &mut TestAppContext) {
        a_load_stops_a_running_filter_steps(cx);
    }

    /// Runs the steps of [`a_load_stops_a_running_filter`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_load_stops_a_running_filter`] says.
    fn a_load_stops_a_running_filter_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        let panel = showing_sample(&workspace, cx);
        panel.update_in(cx, |panel, window, cx| {
            panel
                .filter
                .update(cx, |editor, cx| editor.set_text("zz", window, cx));
        });
        let binary = panel.read_with(cx, |panel, _| panel.binary().clone());
        let missing = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        binary.update(cx, |binary, cx| binary.open_path(missing.clone(), cx));
        let labels: Vec<_> = cx.update(|_, cx| Jobs::running(cx));
        let labels: Vec<_> = labels.into_iter().map(|(_, label, _)| label).collect();
        assert_eq!(labels, [Empty::Reading(missing).says()]);
        cx.run_until_parked();
        panel.read_with(cx, |panel, cx| {
            assert!(panel.rows().is_none());
            assert!(matches!(panel.empty(cx), Some(Empty::LoadFailed(_))));
            assert!(panel.filter_settled(panel.filter_ticket()));
        });
    }

    /// A filter typed again before the engine answered raises the first request's flag at
    /// once, and the rows shown are the second query's.
    ///
    /// # Panics
    ///
    /// Panics if the first flag stays low or the rows answer the first query.
    #[gpui::test]
    fn a_superseded_functions_filter_raises_its_cancel(cx: &mut TestAppContext) {
        a_superseded_functions_filter_raises_its_cancel_steps(cx);
    }

    /// Runs the steps of [`a_superseded_functions_filter_raises_its_cancel`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_superseded_functions_filter_raises_its_cancel`]
    /// says.
    fn a_superseded_functions_filter_raises_its_cancel_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        let panel = showing_sample(&workspace, cx);
        let filter = |text: &'static str, cx: &mut VisualTestContext| {
            panel.update_in(cx, |panel, window, cx| {
                panel
                    .filter
                    .update(cx, |editor, cx| editor.set_text(text, window, cx));
            });
            let jobs = cx.update(|_, cx| Jobs::running(cx));
            let mut flags = jobs
                .into_iter()
                .filter(|(_, label, _)| label == "Filtering functions");
            flags.next().map(|(_, _, flag)| flag)
        };
        let first = filter("zz", cx).unwrap();
        assert!(!first.is_raised());
        filter("zzz", cx);
        assert!(first.is_raised());
        draw(cx);
        let empty = panel.read_with(cx, |panel, cx| panel.empty(cx));
        assert_eq!(empty, Some(Empty::NoMatch("zzz".into())));
    }

    /// A finished load emits `Opened` once and a started or failed one `Closed`; the panel
    /// lists the binary and opens its first function, clears while a load runs, and lists
    /// again on the next finished load.
    ///
    /// # Panics
    ///
    /// Panics if the events or the panel say otherwise.
    #[gpui::test]
    fn the_functions_panel_follows_opened_and_closed(cx: &mut TestAppContext) {
        the_functions_panel_follows_opened_and_closed_steps(cx);
    }

    /// Runs the steps of [`the_functions_panel_follows_opened_and_closed`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_functions_panel_follows_opened_and_closed`]
    /// says.
    fn the_functions_panel_follows_opened_and_closed_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        let panel = panel_of(&workspace, cx);
        let binary = panel.read_with(cx, |panel, _| panel.binary().clone());
        let seen = Rc::new(RefCell::new(Vec::new()));
        let log = seen.clone();
        let _events = cx.update(|_, cx| {
            cx.subscribe(&binary, move |_, event: &BinaryEvent, _| {
                log.borrow_mut()
                    .push(matches!(event, BinaryEvent::Opened(_)));
            })
        });
        let listed = |cx: &mut VisualTestContext| {
            panel.read_with(cx, |panel, _| panel.rows().map(|rows| rows.rows.len()))
        };
        let loaded = sample();
        let all = Some(loaded.initial_rows.rows.len());
        let first = loaded.initial_rows.rows.first().map(|row| row.entry);
        binary.update(cx, |binary, cx| {
            binary.finish_load(Ok(loaded.clone()), cx);
        });
        cx.run_until_parked();
        assert_eq!(*seen.borrow(), [true]);
        assert_eq!(listed(cx), all);
        assert_eq!(shown(&workspace, cx).map(|(entry, _)| entry), first);
        let missing = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        binary.update(cx, |binary, cx| binary.open_path(missing.clone(), cx));
        assert_eq!(*seen.borrow(), [true, false]);
        assert_eq!(listed(cx), None);
        let reading = panel.read_with(cx, |panel, cx| panel.empty(cx));
        assert_eq!(reading, Some(Empty::Reading(missing)));
        cx.run_until_parked();
        assert_eq!(*seen.borrow(), [true, false, false]);
        binary.update(cx, |binary, cx| {
            binary.finish_load(Ok(loaded), cx);
        });
        assert_eq!(*seen.borrow(), [true, false, false, true]);
        assert_eq!(listed(cx), all);
    }

    /// An edit asks the table again over the state it left under the filter typed, which
    /// stays, with the selected row kept by its place, not its index.
    ///
    /// # Panics
    ///
    /// Panics if the filter, the selected place or the shown state is lost.
    #[gpui::test]
    fn an_edit_keeps_a_tables_filter_and_selection(cx: &mut TestAppContext) {
        an_edit_keeps_a_tables_filter_and_selection_steps(cx);
    }

    /// Runs the steps of [`an_edit_keeps_a_tables_filter_and_selection`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`an_edit_keeps_a_tables_filter_and_selection`]
    /// says.
    fn an_edit_keeps_a_tables_filter_and_selection_steps(cx: &mut TestAppContext) {
        use crate::binary::Revision as _;
        use crate::rows_panel::Rows as _;
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        let panel = panel_of(&workspace, cx);
        let binary = panel.read_with(cx, |panel, _| panel.binary().clone());
        binary.update(cx, |binary, cx| {
            binary.finish_load(Ok(sample()), cx);
        });
        cx.run_until_parked();
        let filter = panel.read_with(cx, |panel, _| panel.filter.clone());
        cx.update(|window, cx| filter.update(cx, |editor, cx| editor.set_text("0", window, cx)));
        cx.run_until_parked();
        panel.update(cx, |panel, cx| panel.select(1, cx));
        let callee = Some(Place::Code {
            entry: CALLEE,
            form: Form::Decompile,
            at: None,
        });
        assert_eq!(
            panel.read_with(cx, |panel, _| panel.selected_place()),
            callee
        );
        let rename = borer_engine::analysis::edit::Edit::Name {
            at: CALLER,
            name: "caller_0".to_owned(),
        };
        binary.update(cx, |binary, cx| binary.plan_and_commit(&[rename], cx));
        cx.run_until_parked();
        let now = binary.read_with(cx, |binary, _| binary.loaded().map(|l| l.fingerprint));
        let (text, place, revision, names) = panel.read_with(cx, |panel, cx| {
            let names: Vec<String> = panel
                .rows()
                .map(|rows| rows.rows.iter().map(|row| row.name.clone()).collect())
                .unwrap_or_default();
            let text = panel.filter.read(cx).text(cx);
            (text, panel.selected_place(), panel.revision(), names)
        });
        assert_eq!(text, "0");
        assert_eq!(place, callee);
        assert_eq!(revision, now);
        assert!(names.iter().any(|name| name == "caller_0"), "{names:?}");
    }

    /// Enter on a function row opens that function's decompile view.
    ///
    /// # Panics
    ///
    /// Panics if a row names another place.
    #[test]
    fn a_functions_row_names_the_place_enter_opens() {
        for row in &rows_at(&[0x1000, 0x2000, 0x3000]).rows {
            let want = Place::Code {
                entry: row.entry,
                form: Form::Decompile,
                at: None,
            };
            assert_eq!(Functions::place(row), Some(want));
        }
    }

    /// With no binary the panel draws its card and no column header; once it has rows it
    /// draws the headers.
    ///
    /// # Panics
    ///
    /// Panics if a header is drawn without a binary, or none with rows.
    #[gpui::test]
    fn a_rows_panel_shows_a_card_never_headers_without_a_binary(cx: &mut TestAppContext) {
        a_rows_panel_shows_a_card_never_headers_without_a_binary_steps(cx);
    }

    /// Runs the steps of [`a_rows_panel_shows_a_card_never_headers_without_a_binary`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as
    /// [`a_rows_panel_shows_a_card_never_headers_without_a_binary`] says.
    fn a_rows_panel_shows_a_card_never_headers_without_a_binary_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        draw(cx);
        assert!(cx.debug_bounds(CARD_SELECTOR).is_some());
        assert!(cx.debug_bounds(HEADER_SELECTOR).is_none());
        show_rows(&workspace, rows_at(&[0x1000]), cx);
        assert!(cx.debug_bounds(HEADER_SELECTOR).is_some());
    }

    /// The filter's hint shows the binding the keymap holds for [`FocusFilter`], and a new
    /// binding replaces it.
    ///
    /// # Panics
    ///
    /// Panics if the hint shows no binding or keeps the old one.
    #[gpui::test]
    fn the_filter_hint_follows_the_keymap(cx: &mut TestAppContext) {
        the_filter_hint_follows_the_keymap_steps(cx);
    }

    /// Runs the steps of [`the_filter_hint_follows_the_keymap`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_filter_hint_follows_the_keymap`] says.
    fn the_filter_hint_follows_the_keymap_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (workspace, cx) = open_docked(&app_state, cx);
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        let hint = |cx: &mut VisualTestContext| {
            cx.update(|window, cx| {
                FunctionsPanel::filter_hint(cx).keyboard_shortcut_text(window, cx)
            })
        };
        let before = hint(cx);
        assert!(before.is_some(), "the hint shows no binding");
        cx.update(|_, cx| {
            let rebound = gpui::KeyBinding::new("ctrl-alt-9", FocusFilter, Some("Workspace"));
            cx.bind_keys([rebound]);
        });
        let after = hint(cx);
        assert_ne!(after, before);
        assert!(
            after.as_ref().is_some_and(|text| text.ends_with('9')),
            "{after:?}"
        );
    }
}
