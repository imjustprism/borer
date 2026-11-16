//! Where the app shows something: the one typed place every opener, link, row and tab
//! names, and the one way to open it.

use std::sync::Arc;

use gpui::{App, AppContext as _, Context, Entity, WeakEntity, Window};
use workspace::{Item, ItemHandle, Workspace};

use crate::binary::Binary;
use crate::decompile_item::{DecompileItem, Form, TabMode};
use crate::linear_item::LinearItem;
use crate::overview::OverviewItem;
use crate::worker::LoadedBinary;

/// Where the app shows something; addresses and enums only, never a snapshot or an entity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Place {
    /// One view of the function at `entry`, with the instruction at `at` on its top line
    /// when one is given.
    Code {
        /// Entry virtual address of the function.
        entry: u64,
        /// Which view of it.
        form: Form,
        /// Virtual address of the instruction to show, if any.
        at: Option<u64>,
    },
    /// The engine's triage of the binary: what it is, what it can do, where to start.
    Overview,
    /// The whole image as one listing in address order, with the row holding `at` on its
    /// top line when one is given.
    Linear {
        /// Virtual address to show, if any.
        at: Option<u64>,
    },
}

impl Place {
    /// Returns the decompile view of the function at `entry`, at its start.
    ///
    /// # Arguments
    ///
    /// * `entry` - Entry virtual address of the function.
    #[must_use]
    pub const fn decompile(entry: u64) -> Self {
        Self::Code {
            entry,
            form: Form::Decompile,
            at: None,
        }
    }
}

/// How a place opens: a new tab's kind, and whether the tab, new or already open, takes
/// keyboard focus; a permanent opening also keeps a preview tab already showing the place.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Opening {
    /// Whether a new tab is the preview tab or a permanent one.
    pub mode: TabMode,
    /// Whether the tab takes keyboard focus.
    pub focus: bool,
}

/// Shows `place` of `loaded` in the workspace's active pane.
///
/// It activates the tab already showing the place for the same program, else opens one as
/// `how` says; a place with an address puts the line that starts at that instruction (in
/// the linear listing, the row holding it) at the top, now or once the view is built, and
/// a code view moves nowhere when no line starts there.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary, whose status line and drops the tab uses.
/// * `loaded` - The snapshot the place is shown from.
/// * `place` - What to show.
/// * `how` - How a new tab opens.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn open(
    workspace: &mut Workspace,
    binary: &Entity<Binary>,
    loaded: &Arc<LoadedBinary>,
    place: Place,
    how: Opening,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    let (binary, loaded) = (binary.clone(), loaded.clone());
    let program = loaded.program.clone();
    match place {
        Place::Code { entry, form, at } => {
            let shows = |item: &DecompileItem| {
                item.entry() == Some(entry)
                    && item.form() == form
                    && Arc::ptr_eq(&item.loaded().program, &program)
            };
            let build = |weak, window: &mut Window, cx: &mut Context<'_, DecompileItem>| {
                DecompileItem::function(weak, binary, loaded, (entry, form), window, cx)
            };
            let item = show(workspace, how, shows, build, window, cx);
            if let Some(va) = at {
                item.update(cx, |item, cx| item.go_to_address(va, cx));
            }
        }
        Place::Overview => {
            let shows = |item: &OverviewItem| Arc::ptr_eq(&item.loaded().program, &program);
            let build = |weak, _: &mut Window, cx: &mut Context<'_, OverviewItem>| {
                OverviewItem::new(weak, binary, loaded, cx)
            };
            show(workspace, how, shows, build, window, cx);
        }
        Place::Linear { at } => {
            let shows = |item: &LinearItem| Arc::ptr_eq(&item.loaded().program, &program);
            let build = |weak, window: &mut Window, cx: &mut Context<'_, LinearItem>| {
                LinearItem::new(weak, binary, loaded, window, cx)
            };
            let item = show(workspace, how, shows, build, window, cx);
            if let Some(va) = at {
                item.update(cx, |item, cx| item.go_to(va, window, cx));
            }
        }
    }
}

/// Activates the tab of type `T` in the active pane that `shows` picks, else opens the one
/// `build` makes as `how` says.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `how` - How a new tab opens; a permanent opening also keeps a preview tab it finds.
/// * `shows` - Whether a tab already shows what is asked for.
/// * `build` - Makes the new tab.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
///
/// # Returns
///
/// The tab, found or new.
fn show<T: Item>(
    workspace: &Workspace,
    how: Opening,
    shows: impl Fn(&T) -> bool,
    build: impl FnOnce(WeakEntity<Workspace>, &mut Window, &mut Context<'_, T>) -> T,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) -> Entity<T> {
    let weak = workspace.weak_handle();
    let pane = workspace.active_pane().clone();
    let existing = pane
        .read(cx)
        .items_of_type::<T>()
        .find(|item| shows(item.read(cx)));
    pane.update(cx, |pane, cx| {
        if let Some(item) = existing {
            if how.mode == TabMode::Permanent {
                pane.unpreview_item_if_preview(item.entity_id());
            }
            if let Some(ix) = pane.index_for_item(&item) {
                pane.activate_item(ix, true, how.focus, window, cx);
            }
            return item;
        }
        let ix = match how.mode {
            TabMode::Preview => pane.close_current_preview_item(window, cx),
            TabMode::Permanent => None,
        };
        let item = cx.new(|cx| build(weak, window, cx));
        let id = item.entity_id();
        pane.add_item(Box::new(item.clone()), true, how.focus, ix, window, cx);
        if how.mode == TabMode::Preview {
            pane.replace_preview_item_id(id, window, cx);
        }
        item
    })
}

/// Returns the snapshot the active center item shows, else the window's binary's.
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `binary` - The window's binary.
/// * `cx` - Application context reading them.
///
/// # Returns
///
/// The snapshot, `None` before a binary is loaded.
#[must_use]
pub fn shown_binary(
    workspace: &Workspace,
    binary: &Entity<Binary>,
    cx: &App,
) -> Option<Arc<LoadedBinary>> {
    let active = workspace.active_item(cx);
    let shown = active
        .as_ref()
        .and_then(|item| loaded_of(item.as_ref(), cx));
    shown.or_else(|| binary.read(cx).loaded()).cloned()
}

/// Returns the snapshot a center item shows, `None` for an item that shows none.
///
/// # Arguments
///
/// * `item` - The item.
/// * `cx` - Application context reading it.
fn loaded_of<'a>(item: &dyn ItemHandle, cx: &'a App) -> Option<&'a Arc<LoadedBinary>> {
    if let Some(code) = item.downcast::<DecompileItem>() {
        return Some(code.read(cx).loaded());
    }
    if let Some(overview) = item.downcast::<OverviewItem>() {
        return Some(overview.read(cx).loaded());
    }
    Some(item.downcast::<LinearItem>()?.read(cx).loaded())
}

/// Returns the place a center item shows.
///
/// # Arguments
///
/// * `item` - The item.
/// * `cx` - Application context reading it.
///
/// # Returns
///
/// The function and view a code tab shows, with no address (a tab keeps no address, only
/// its scroll), the overview or the linear listing; `None` for the start tab and for
/// measured lines.
#[must_use]
pub fn place_of(item: &dyn ItemHandle, cx: &App) -> Option<Place> {
    if item.downcast::<OverviewItem>().is_some() {
        return Some(Place::Overview);
    }
    if item.downcast::<LinearItem>().is_some() {
        return Some(Place::Linear { at: None });
    }
    let item = item.downcast::<DecompileItem>()?;
    let item = item.read(cx);
    Some(Place::Code {
        entry: item.entry()?,
        form: item.form(),
        at: None,
    })
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use workspace::Workspace;

    use std::sync::Arc;

    use super::{Place, place_of};
    use crate::app_view::tests::{CALLER, init, open, open_place, sample};
    use crate::decompile_item::tests::{active, fourth_instruction};
    use crate::decompile_item::{Form, TabMode};
    use crate::worker::LoadedBinary;

    /// Returns how many tabs of the active pane show `place`, and the active tab's place.
    fn tabs_of(
        workspace: &Entity<Workspace>,
        place: Place,
        cx: &mut VisualTestContext,
    ) -> (usize, Option<Place>) {
        workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            let count = pane
                .items()
                .filter(|item| place_of(item.as_ref(), cx) == Some(place))
                .count();
            let shown = pane
                .active_item()
                .and_then(|item| place_of(item.as_ref(), cx));
            (count, shown)
        })
    }

    /// Each code place opened twice leaves one tab, which names the place; a listing at an
    /// address has that instruction's line at its top.
    #[gpui::test]
    fn every_place_opens_one_tab_and_names_itself(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let (va, line) = fourth_instruction(&loaded);
        let code = |form, at| Place::Code {
            entry: CALLER,
            form,
            at,
        };
        let places = [
            (code(Form::Decompile, None), 0),
            (code(Form::Listing, None), 0),
            (code(Form::Listing, Some(va)), line),
        ];
        for (place, top) in places {
            for _ in 0..2 {
                open_place(&workspace, &loaded, place, TabMode::Permanent, cx);
                cx.run_until_parked();
            }
            let Place::Code { form, .. } = place else {
                continue;
            };
            let named = code(form, None);
            assert_eq!(
                tabs_of(&workspace, named, cx),
                (1, Some(named)),
                "{place:?}"
            );
            assert_eq!(
                active(&workspace, cx),
                Some((CALLER, form, top)),
                "{place:?}"
            );
        }
    }

    /// A tab is one per program and place: the same place of two loads of one file opens
    /// two tabs, and of a renamed overlay over the same program reuses the one.
    #[gpui::test]
    fn a_place_is_one_tab_per_program(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let first = sample();
        let place = Place::decompile(CALLER);
        let tabs = |cx: &mut VisualTestContext| tabs_of(&workspace, place, cx).0;
        open_place(&workspace, &first, place, TabMode::Permanent, cx);
        open_place(&workspace, &sample(), place, TabMode::Permanent, cx);
        assert_eq!(tabs(cx), 2);
        let mut overlay = (*first.overlay).clone();
        overlay.names.insert(CALLER, "renamed".to_owned());
        let renamed = Arc::new(LoadedBinary {
            path: first.path.clone(),
            program: first.program.clone(),
            analysis: first.analysis.clone(),
            overlay: Arc::new(overlay),
            initial_rows: first.initial_rows.clone(),
        });
        open_place(&workspace, &renamed, place, TabMode::Permanent, cx);
        assert_eq!(tabs(cx), 2);
    }
}
