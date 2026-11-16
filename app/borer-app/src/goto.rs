//! Go to: Zed's picker over what the person types.
//!
//! The engine resolves the text as an address or a name in the background and filters the
//! function rows by it; Enter opens the function, a listing at the resolved instruction when
//! a listing is the active view. A miss shows the engine's own words, nearest names and all.

use std::sync::Arc;

use gpui::{App, Context, DismissEvent, Task, WeakEntity, Window};
use picker::{Picker, PickerDelegate};
use ui::{Color, Label, LabelCommon as _, ListItem, ListItemSpacing, prelude::*};
use workspace::Workspace;

use crate::decompile_item::{DecompileItem, Form, TabMode, open_function, open_listing};
use crate::functions_panel::FunctionsPanel;
use crate::worker::{GoToAnswer, LoadedBinary, goto_blocking, spawn_engine};

gpui::actions!(
    borer,
    [
        /// Opens the go-to picker: an address or a name opens the function holding it, and
        /// the functions whose names match are listed below it.
        GoTo,
    ]
);

/// One line of the picker.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Match {
    /// The function holding what the text resolves to: its entry and the address.
    Target(u64, u64),
    /// The engine's words for a text that resolves to no function.
    Miss(String),
    /// A function row the text filters: its entry and its name.
    Row(u64, String),
    /// How many rows are shown, and how many the text filters in all.
    Count(usize, usize),
}

impl Match {
    /// Returns the entry this line opens and the address to show in it, `None` for a line
    /// that opens nothing.
    const fn opens(&self) -> Option<(u64, Option<u64>)> {
        match self {
            Self::Target(entry, va) => Some((*entry, Some(*va))),
            Self::Row(entry, _) => Some((*entry, None)),
            Self::Miss(_) | Self::Count(..) => None,
        }
    }
}

/// Returns the picker's lines for an answer: the resolved function or the miss first when
/// the text is not empty, then the rows, then how many of how many they are.
///
/// # Arguments
///
/// * `query` - The text, trimmed.
/// * `answer` - What the engine found for it.
fn lines(query: &str, answer: GoToAnswer) -> Vec<Match> {
    let first = (!query.is_empty()).then_some(match answer.target {
        Ok((entry, va)) => Match::Target(entry, va),
        Err(miss) => Match::Miss(miss),
    });
    let count = Match::Count(answer.rows.rows.len(), answer.rows.total);
    let rows = answer
        .rows
        .rows
        .into_iter()
        .map(|r| Match::Row(r.entry, r.name));
    first.into_iter().chain(rows).chain([count]).collect()
}

/// The go-to picker's state: the binary it searches and the lines of the latest answer.
#[derive(Debug)]
pub struct GoToDelegate {
    /// Workspace a confirmed line opens its function in.
    workspace: WeakEntity<Workspace>,
    /// Binary the text is resolved in.
    loaded: Arc<LoadedBinary>,
    /// The view of the active code tab, which a confirmed line opens.
    form: Form,
    /// The lines of the latest answer.
    matches: Vec<Match>,
    /// The selected line.
    selected: usize,
}

/// Opens the go-to picker over the binary of the active code tab, else of the functions
/// panel; nothing opens before a binary is loaded.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn toggle(workspace: &mut Workspace, window: &mut Window, cx: &mut Context<'_, Workspace>) {
    let tab = workspace.active_item_as::<DecompileItem>(cx);
    let form = tab
        .as_ref()
        .map_or(Form::Decompile, |item| item.read(cx).form());
    let tab = tab.map(|item| item.read(cx).loaded().clone());
    let panel = || {
        let panel = workspace.panel::<FunctionsPanel>(cx)?;
        panel.read(cx).binary().read(cx).loaded().cloned()
    };
    let Some(loaded) = tab.or_else(panel) else {
        return;
    };
    let delegate = GoToDelegate {
        workspace: workspace.weak_handle(),
        loaded,
        form,
        matches: Vec::new(),
        selected: 0,
    };
    workspace.toggle_modal(window, cx, |window, cx| {
        Picker::uniform_list(delegate, window, cx)
    });
}

impl PickerDelegate for GoToDelegate {
    type ListItem = ListItem;

    fn name() -> &'static str {
        "borer go to"
    }

    fn match_count(&self) -> usize {
        self.matches.len()
    }

    fn selected_index(&self) -> usize {
        self.selected
    }

    fn set_selected_index(
        &mut self,
        ix: usize,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) {
        self.selected = ix;
    }

    fn can_select(
        &self,
        ix: usize,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> bool {
        self.matches.get(ix).is_some_and(|m| m.opens().is_some())
    }

    fn placeholder_text(&self, _window: &mut Window, _cx: &mut App) -> Arc<str> {
        "Go to an address or a name".into()
    }

    fn update_matches(
        &mut self,
        query: String,
        _window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) -> Task<()> {
        let loaded = self.loaded.clone();
        let label = format!("Going to {}", query.trim());
        let answer = spawn_engine(label, cx, move || {
            let query = query.trim();
            lines(query, goto_blocking(&loaded, query))
        });
        cx.spawn(async move |picker, cx| {
            let (Some(matches), Some(picker)) = (answer.await, picker.upgrade()) else {
                return;
            };
            picker.update(cx, |picker, cx| {
                let delegate = &mut picker.delegate;
                delegate.selected = matches
                    .iter()
                    .position(|m| m.opens().is_some())
                    .unwrap_or(0);
                delegate.matches = matches;
                cx.notify();
            });
        })
    }

    fn confirm(
        &mut self,
        _secondary: bool,
        window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) {
        let Some((entry, at)) = self.matches.get(self.selected).and_then(Match::opens) else {
            return;
        };
        let (workspace, loaded, form) = (self.workspace.clone(), self.loaded.clone(), self.form);
        cx.emit(DismissEvent);
        window.defer(cx, move |window, cx| {
            let Some(workspace) = workspace.upgrade() else {
                return;
            };
            workspace.update(cx, |workspace, cx| match form {
                Form::Listing => open_listing(workspace, loaded, (entry, at), window, cx),
                Form::Decompile => {
                    let mode = TabMode::Permanent;
                    open_function(workspace, loaded, entry, mode, true, window, cx);
                }
            });
        });
    }

    fn dismissed(&mut self, _window: &mut Window, cx: &mut Context<'_, Picker<Self>>) {
        cx.emit(DismissEvent);
    }

    fn render_match(
        &self,
        ix: usize,
        selected: bool,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> Option<Self::ListItem> {
        let (text, color) = match self.matches.get(ix)? {
            Match::Target(entry, va) => (
                format!("open the function at {entry:#x}, which holds {va:#x}"),
                Color::Default,
            ),
            Match::Miss(miss) => (miss.clone(), Color::Muted),
            Match::Row(entry, name) => (format!("{entry:#x}  {name}"), Color::Default),
            Match::Count(shown, total) => (format!("showing {shown} of {total}"), Color::Muted),
        };
        Some(
            ListItem::new(ix)
                .inset(true)
                .spacing(ListItemSpacing::Sparse)
                .toggle_state(selected)
                .child(Label::new(text).color(color)),
        )
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::resolve_suggesting;
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use picker::Picker;
    use workspace::Workspace;

    use super::{GoToDelegate, Match};
    use crate::app_view::tests::{CALLEE, CALLER, init, open, sample};
    use crate::decompile_item::tests::{active as tab, fourth_instruction, open_tab};
    use crate::decompile_item::{DecompileItem, Form};
    use crate::worker::{Jobs, LoadedBinary};

    /// Opens go to with its key from the focused code tab, types `query` and waits for the
    /// engine's answer.
    ///
    /// # Panics
    ///
    /// Panics if the picker does not open.
    fn ask(
        workspace: &Entity<Workspace>,
        query: &str,
        cx: &mut VisualTestContext,
    ) -> Entity<Picker<GoToDelegate>> {
        cx.simulate_keystrokes("g");
        cx.run_until_parked();
        let picker = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_modal::<Picker<GoToDelegate>>(cx)
            })
            .unwrap();
        picker.update_in(cx, |picker, window, cx| picker.set_query(query, window, cx));
        cx.run_until_parked();
        picker
    }

    /// Returns the entry of the active code tab.
    fn active(workspace: &Entity<Workspace>, cx: &mut VisualTestContext) -> Option<u64> {
        workspace.read_with(cx, |workspace, cx| {
            workspace
                .active_item_as::<DecompileItem>(cx)?
                .read(cx)
                .entry()
        })
    }

    /// Going to an address and to a name opens the function, and a near miss shows the
    /// engine's answer, nearest name and all, and opens nothing.
    ///
    /// # Panics
    ///
    /// Panics if go to opens the wrong function or says other than the engine.
    #[gpui::test]
    fn go_to_opens_what_the_engine_resolves(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let plain = sample();
        let mut overlay = (*plain.overlay).clone();
        overlay.names.insert(CALLER, "caller_fn".to_owned());
        overlay.names.insert(CALLEE, "callee_fn".to_owned());
        let loaded = Arc::new(LoadedBinary {
            path: plain.path.clone(),
            program: plain.program.clone(),
            analysis: plain.analysis.clone(),
            overlay: Arc::new(overlay),
            initial_rows: plain.initial_rows.clone(),
        });
        open_tab(&workspace, &loaded, (CALLER, Form::Decompile), cx);
        for (query, want) in [
            (format!("{CALLEE:#x}"), CALLEE),
            ("caller_fn".to_owned(), CALLER),
        ] {
            ask(&workspace, &query, cx);
            cx.dispatch_action(menu::Confirm);
            cx.run_until_parked();
            assert_eq!(active(&workspace, cx), Some(want), "{query}");
        }
        let picker = ask(&workspace, "calee_fn", cx);
        let said = resolve_suggesting(
            &loaded.program,
            &loaded.analysis,
            &loaded.overlay,
            "calee_fn",
        );
        let miss = said.unwrap_err();
        assert!(miss.contains("callee_fn"), "{miss}");
        let (first, last) = picker.read_with(cx, |picker, _| {
            let matches = &picker.delegate.matches;
            (matches.first().cloned(), matches.last().cloned())
        });
        assert_eq!(first, Some(Match::Miss(miss)));
        assert_eq!(last, Some(Match::Count(0, 0)));
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        assert_eq!(active(&workspace, cx), Some(CALLER));
    }

    /// A query typed again before the engine answered lists the second query's answer;
    /// each query runs as a listed request.
    #[gpui::test]
    fn a_go_to_query_typed_over_lists_the_newest_answer(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        open_tab(&workspace, &sample(), (CALLER, Form::Decompile), cx);
        let picker = ask(&workspace, "", cx);
        let query = |text: &str, cx: &mut VisualTestContext| {
            picker.update_in(cx, |picker, window, cx| picker.set_query(text, window, cx));
            let jobs = cx.update(|_, cx| Jobs::running(cx));
            let label = format!("Going to {text}");
            let mut flags = jobs.into_iter().filter(|(_, l, _)| *l == label);
            flags.next().map(|(_, _, flag)| flag)
        };
        assert!(query("0x1", cx).is_some());
        query(&format!("{CALLEE:#x}"), cx);
        cx.run_until_parked();
        let opens = picker.read_with(cx, |picker, _| picker.delegate.matches.first().cloned());
        assert_eq!(opens.and_then(|m| m.opens()), Some((CALLEE, Some(CALLEE))));
    }

    /// From a listing tab, going to an address inside a function opens that function's
    /// listing at the line of the instruction, and the picker counts the rows it shows.
    ///
    /// # Panics
    ///
    /// Panics if the listing opens elsewhere or the count is missing.
    #[gpui::test]
    fn go_to_from_a_listing_opens_the_instruction(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let (va, line) = fourth_instruction(&loaded);
        open_tab(&workspace, &loaded, (CALLER, Form::Listing), cx);
        let picker = ask(&workspace, &format!("{va:#x}"), cx);
        let last = picker.read_with(cx, |picker, _| picker.delegate.matches.last().cloned());
        assert!(matches!(last, Some(Match::Count(..))));
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        let shown = tab(&workspace, cx);
        assert_eq!(shown, Some((CALLER, Form::Listing, line)));
    }
}
