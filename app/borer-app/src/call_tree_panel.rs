//! The call tree panel: the callers or callees of one function of the open binary as a tree
//! in a Zed dock.
//!
//! Each node's level is read from the engine in the background when it opens. A click
//! opens a row in the preview tab, Enter in a permanent one: a node its function, a call
//! site its caller's listing at the instruction.

use std::collections::BTreeMap;
use std::ops::Range;
use std::sync::Arc;

use borer_engine::analysis::render::Via;
use gpui::{
    Action, AnyElement, App, AppContext as _, Context, Entity, EventEmitter, FocusHandle,
    Focusable, Font, FontWeight, InteractiveElement as _, IntoElement, ParentElement as _, Render,
    ScrollStrategy, SharedString, Styled as _, Subscription, UniformListScrollHandle, WeakEntity,
    Window, div, px, uniform_list,
};
use settings::Settings as _;
use smallvec::SmallVec;
use theme::ActiveTheme as _;
use theme_settings::ThemeSettings;
use ui::{
    Color, IconName, IndentGuideColors, Label, LabelCommon as _, LabelSize, ListItem,
    ListItemSpacing, Toggleable as _, h_flex, indent_guides,
};
use workspace::Workspace;
use workspace::dock::{DockPosition, Panel, PanelEvent};

use crate::actions::ToggleVirtualCalls;
use crate::actions::{CallTree as CallTreeAction, CallTreeDirection, Hint, ShowCallSites};
use crate::app_assets::Glyph;
use crate::binary::{Binary, BinaryEvent};
use crate::call_tree::{Answer, CallTree, Direction, Missing, Row, Shape, Virtuals, via_label};
use crate::card::{Card, Tone};
use crate::code_view::{CodePalette, Role};
use crate::decompile_item::{DecompileItem, TabMode};
use crate::panels::{PanelSpec, remove, spec_panel};
use crate::places::{Opening, open};
use crate::rows_panel::Empty;
use crate::worker::{Job, LoadedBinary, call_level_blocking, function_name_blocking};

/// The call tree panel's row of [`crate::panels::PANELS`].
pub const PANEL: PanelSpec = PanelSpec {
    key: "CallTree",
    title: "Call tree",
    icon: Glyph::Zed(IconName::GitGraph),
    toggle: &CallTreeAction,
    dock: DockPosition::Bottom,
    docks: &[
        DockPosition::Left,
        DockPosition::Right,
        DockPosition::Bottom,
    ],
    size_px: 280.0,
    hooks: crate::rail::panel::<CallTreePanel>(),
    add: |workspace, binary, dock, window, cx| {
        let weak = cx.weak_entity();
        let panel = cx.new(|cx| CallTreePanel::new(weak, binary, dock, cx));
        workspace.add_panel(panel, window, cx);
    },
    remove: remove::<CallTreePanel>,
    focus: root_and_focus,
};

/// Roots the call tree at the function of the active code tab, when one is active, and
/// focuses its panel, or moves focus back when the panel has it: the call tree row's
/// [`PanelSpec::focus`].
///
/// # Arguments
///
/// * `workspace` - The workspace.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
fn root_and_focus(workspace: &mut Workspace, window: &mut Window, cx: &mut Context<'_, Workspace>) {
    let panel = workspace.panel::<CallTreePanel>(cx);
    if panel.is_some_and(|panel| panel.focus_handle(cx).contains_focused(window, cx)) {
        workspace.toggle_panel_focus::<CallTreePanel>(window, cx);
        return;
    }
    let active = workspace.active_item_as::<DecompileItem>(cx);
    let root = active.and_then(|item| {
        let item = item.read(cx);
        Some((item.loaded().clone(), item.entry()?))
    });
    if let (Some((loaded, entry)), Some(panel)) = (root, workspace.panel::<CallTreePanel>(cx)) {
        panel.update(cx, |panel, cx| panel.set_root(&loaded, entry, cx));
    }
    workspace.focus_panel::<CallTreePanel>(window, cx);
}

/// The actions the panel answers in its own `on_action`, about the tree it shows, so they
/// are available only while it has focus.
pub const OWN_ACTIONS: &[&dyn Action] = &[&CallTreeDirection, &ToggleVirtualCalls, &ShowCallSites];

/// The hint the panel offers while no tree is rooted.
const ROOT_HINT: Hint = (
    &CallTreeAction,
    "Root the tree at the active tab's function",
);

/// Logical pixels each level of the tree is indented by.
const INDENT_PX: f32 = 12.0;

/// Height in logical pixels of every row, the design's table row.
const ROW_HEIGHT_PX: f32 = 22.0;

/// A tree rooted in the open binary, with the reads that fill it.
struct Rooted {
    /// The binary the tree's functions belong to, the one open when it was rooted.
    loaded: Arc<LoadedBinary>,
    /// What is open and selected.
    tree: CallTree,
    /// Each node's newest level read, by node; dropping one raises its read's cancel.
    reads: BTreeMap<u64, Job>,
}

/// The callers or callees of one function, as a tree in a dock.
pub struct CallTreePanel {
    /// Workspace the panel opens functions and listings in.
    workspace: WeakEntity<Workspace>,
    /// Focus handle of the panel's root.
    focus_handle: FocusHandle,
    /// The binary whose functions the tree roots in.
    binary: Entity<Binary>,
    /// The tree, once a root is set in the open binary.
    rooted: Option<Rooted>,
    /// Scroll handle of the virtualized rows.
    scroll: UniformListScrollHandle,
    /// Dock the panel sits in.
    position: DockPosition,
    /// Follows the binary's changes.
    _subscriptions: [Subscription; 1],
}

impl std::fmt::Debug for CallTreePanel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CallTreePanel")
            .field("tree", &self.tree())
            .finish_non_exhaustive()
    }
}

impl CallTreePanel {
    /// Returns an empty panel over the functions of `binary`.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the panel opens functions and listings in.
    /// * `binary` - The binary whose functions the tree roots in.
    /// * `position` - Dock the panel starts in.
    /// * `cx` - Panel context.
    #[must_use]
    pub fn new(
        workspace: WeakEntity<Workspace>,
        binary: &Entity<Binary>,
        position: DockPosition,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        Self {
            workspace,
            focus_handle: cx.focus_handle(),
            binary: binary.clone(),
            rooted: None,
            scroll: UniformListScrollHandle::new(),
            position,
            _subscriptions: [cx.subscribe(binary, |this, _, event, cx| {
                this.follow_binary(event, cx);
            })],
        }
    }

    /// Returns the tree, once a root is set.
    #[must_use]
    pub fn tree(&self) -> Option<&CallTree> {
        self.rooted.as_ref().map(|rooted| &rooted.tree)
    }

    /// Returns whether a level read of the tree has not been applied yet.
    #[must_use]
    pub fn is_reading(&self) -> bool {
        self.rooted
            .as_ref()
            .is_some_and(|rooted| rooted.reads.values().any(Job::is_running))
    }

    /// Roots the tree at the function at `root`, when `loaded` is the binary open, and reads
    /// the root's level; the direction and virtuals setting carry over from the tree before.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The binary the function belongs to.
    /// * `root` - Entry of the function.
    /// * `cx` - Panel context.
    pub fn set_root(&mut self, loaded: &Arc<LoadedBinary>, root: u64, cx: &mut Context<'_, Self>) {
        let open = self.binary.read(cx).loaded();
        if !open.is_some_and(|open| Arc::ptr_eq(open, loaded)) {
            return;
        }
        let (direction, virtuals) = self
            .tree()
            .map_or((Direction::Callees, Virtuals::Hidden), |t| {
                (t.direction(), t.virtuals())
            });
        self.rebuild(loaded.clone(), CallTree::new(root, direction, virtuals), cx);
    }

    /// Flips the tree between callees and callers, keeping its root.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    pub fn flip_direction(&mut self, cx: &mut Context<'_, Self>) {
        let Some(rooted) = self.rooted.as_ref() else {
            return;
        };
        let (tree, loaded) = (&rooted.tree, rooted.loaded.clone());
        let flipped = CallTree::new(tree.root(), tree.direction().flipped(), tree.virtuals());
        self.rebuild(loaded, flipped, cx);
    }

    /// Lists or hides the resolved virtual calls of callees levels, keeping the root; over
    /// callers, where the level stays the same, the tree stays as it is.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    pub fn toggle_virtuals(&mut self, cx: &mut Context<'_, Self>) {
        let Some(rooted) = self.rooted.as_mut() else {
            return;
        };
        let virtuals = rooted.tree.virtuals().toggled();
        if rooted.tree.keep_virtuals(virtuals) {
            cx.notify();
            return;
        }
        let tree = CallTree::new(rooted.tree.root(), rooted.tree.direction(), virtuals);
        let loaded = rooted.loaded.clone();
        self.rebuild(loaded, tree, cx);
    }

    /// Opens or closes row `ix` and selects it.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index.
    /// * `cx` - Panel context.
    pub fn toggle(&mut self, ix: usize, cx: &mut Context<'_, Self>) {
        let Some(rooted) = self.rooted.as_mut() else {
            return;
        };
        rooted.tree.select(ix);
        let ask = rooted.tree.toggle(ix);
        self.read(ask, cx);
        cx.notify();
    }

    /// Lists the call sites of the selected row's call, or hides them.
    ///
    /// # Arguments
    ///
    /// * `cx` - Panel context.
    pub fn toggle_sites(&mut self, cx: &mut Context<'_, Self>) {
        if let Some(rooted) = self.rooted.as_mut()
            && rooted.tree.toggle_sites(rooted.tree.selected())
        {
            cx.notify();
        }
    }

    /// Follows the selected row as `mode` says: a node opens its function's decompile, a
    /// call site the listing of the function making the call at its instruction, and an
    /// import lists its call sites. A permanent tab takes keyboard focus, the preview leaves
    /// it in the tree.
    ///
    /// # Arguments
    ///
    /// * `mode` - Whether the tab is the preview tab or a permanent one.
    /// * `window` - Window the panel is in.
    /// * `cx` - Panel context.
    pub fn confirm(&mut self, mode: TabMode, window: &mut Window, cx: &mut Context<'_, Self>) {
        let Some(rooted) = self.rooted.as_mut() else {
            return;
        };
        let place = rooted
            .tree
            .follow(rooted.tree.selected())
            .map(|f| f.place());
        let loaded = rooted.loaded.clone();
        cx.notify();
        let (Some(place), Some(workspace)) = (place, self.workspace.upgrade()) else {
            return;
        };
        let binary = self.binary.clone();
        let how = Opening {
            mode,
            focus: mode == TabMode::Permanent,
        };
        workspace.update(cx, |workspace, cx| {
            open(workspace, &binary, &loaded, place, how, window, cx);
        });
    }

    /// Selects row `ix` and keeps it on screen.
    ///
    /// # Arguments
    ///
    /// * `ix` - Zero-based row index, clamped to the rows shown.
    /// * `cx` - Panel context.
    pub fn select(&mut self, ix: usize, cx: &mut Context<'_, Self>) {
        if let Some(rooted) = self.rooted.as_mut() {
            rooted.tree.select(ix);
            self.scroll
                .scroll_to_item(rooted.tree.selected(), ScrollStrategy::Nearest);
            cx.notify();
        }
    }

    /// Shows `tree` of `loaded` in place of the tree before, which drops every read of that
    /// one and so raises their cancels, and opens the root.
    ///
    /// # Arguments
    ///
    /// * `loaded` - The binary the tree's functions belong to.
    /// * `tree` - A closed tree.
    /// * `cx` - Panel context.
    fn rebuild(
        &mut self,
        loaded: Arc<LoadedBinary>,
        mut tree: CallTree,
        cx: &mut Context<'_, Self>,
    ) {
        let ask = tree.expand(0);
        self.rooted = Some(Rooted {
            loaded,
            tree,
            reads: BTreeMap::new(),
        });
        self.read(ask, cx);
        self.scroll.scroll_to_item(0, ScrollStrategy::Top);
        cx.notify();
    }

    /// Reads the level of `node`, when one is asked for, in the background, in the node's
    /// slot of the tree's reads; the root's read also names the root.
    ///
    /// # Arguments
    ///
    /// * `node` - The node whose level the tree asked for, if any.
    /// * `cx` - Panel context spawning the read.
    fn read(&mut self, node: Option<u64>, cx: &mut Context<'_, Self>) {
        let (Some(node), Some(rooted)) = (node, self.rooted.as_mut()) else {
            return;
        };
        let loaded = rooted.loaded.clone();
        let named = rooted.tree.root() == node && rooted.tree.root_name().is_none();
        let level = rooted.tree.level();
        let label = match rooted.tree.direction() {
            Direction::Callees => format!("Callees of {node:#x}"),
            Direction::Callers => format!("Callers of {node:#x}"),
        };
        let work = move || {
            let name = named.then(|| function_name_blocking(&loaded, node));
            (name, call_level_blocking(&loaded, node, level))
        };
        let job = rooted.reads.entry(node).or_default();
        job.run(label, cx, work, move |panel: &mut Self, answer, cx| {
            let (name, (children, search)) = answer;
            let Some(rooted) = panel.rooted.as_mut() else {
                return;
            };
            rooted.tree.answer(node, Answer { children, search });
            if let Some(name) = name {
                rooted.tree.name_root(name.into_boxed_str());
            }
            cx.notify();
        });
    }

    /// Follows a change of the window's binary: a load that finished or a binary that
    /// closed drops the tree, which raises the cancel of each of its reads.
    ///
    /// # Arguments
    ///
    /// * `event` - What changed.
    /// * `cx` - Panel context.
    fn follow_binary(&mut self, event: &BinaryEvent, cx: &mut Context<'_, Self>) {
        match event {
            BinaryEvent::Opened(_) | BinaryEvent::Closed => {
                if self.rooted.take().is_some() {
                    cx.notify();
                }
            }
        }
    }

    /// Returns what the panel says while it shows no tree.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the binary.
    ///
    /// # Returns
    ///
    /// The binary's card while none is open, else the card offering a root; `None` once a
    /// tree is rooted.
    #[must_use]
    pub fn card(&self, cx: &App) -> Option<Card> {
        if self.rooted.is_some() {
            return None;
        }
        let binary = self.binary.read(cx);
        if binary.loaded().is_none() {
            return Some(Empty::of_binary(binary).card());
        }
        Some(Card {
            says: "The tree starts at the function of the active tab".into(),
            tone: Tone::Quiet,
            offers: &[ROOT_HINT],
        })
    }

    /// Builds the visible rows in `range` of the tree.
    ///
    /// # Arguments
    ///
    /// * `range` - Visible row index range requested by `uniform_list`.
    /// * `_window` - Window painting the rows.
    /// * `cx` - Panel context.
    ///
    /// # Returns
    ///
    /// One element per row of `range`.
    fn render_rows(
        &mut self,
        range: Range<usize>,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Vec<AnyElement> {
        let Some(tree) = self.tree() else {
            return Vec::new();
        };
        let look = Look {
            palette: CodePalette::from_theme(cx.theme()),
            font: ThemeSettings::get_global(cx).buffer_font.clone(),
        };
        range
            .filter_map(|ix| Some(render_row(tree, ix, tree.rows().get(ix)?, &look, cx)))
            .collect()
    }

    /// Returns the depth of each row in `range`, for the indent guides.
    ///
    /// # Arguments
    ///
    /// * `range` - Row index range the guides are drawn over.
    fn depths(&self, range: Range<usize>) -> SmallVec<[usize; 64]> {
        self.tree().map_or_else(SmallVec::new, |tree| {
            let len = tree.rows().len();
            tree.rows()
                .get(range.start.min(len)..range.end.min(len))
                .unwrap_or_default()
                .iter()
                .map(|row| row.depth() + 1)
                .collect()
        })
    }
}

/// Renders the panel's one-line header: the direction and the root, whether virtual calls
/// are listed, and how much of the root's level the engine lists.
///
/// # Arguments
///
/// * `tree` - The tree.
fn header(tree: &CallTree) -> AnyElement {
    let title = match tree.direction() {
        Direction::Callees => "Callees of",
        Direction::Callers => "Callers of",
    };
    let note = match (tree.direction(), tree.virtuals()) {
        (Direction::Callees, Virtuals::Hidden) => "virtual calls hidden",
        (Direction::Callees, Virtuals::Shown) => "virtual calls listed",
        (Direction::Callers, Virtuals::Hidden | Virtuals::Shown) => "",
    };
    let showing = tree
        .root_level()
        .map(|(shown, total)| format!("showing {shown} of {total}"));
    h_flex()
        .px(px(8.0))
        .py(px(4.0))
        .justify_between()
        .child(
            h_flex()
                .gap_2()
                .child(
                    Label::new(format!("{title} {}", root_label(tree)))
                        .weight(FontWeight::SEMIBOLD),
                )
                .child(muted(note)),
        )
        .children(showing.map(muted))
        .into_any_element()
}

/// What the rows are painted with, read once per frame.
struct Look {
    /// Token colors of the active theme.
    palette: CodePalette,
    /// The buffer font names are drawn in.
    font: Font,
}

/// Returns the root's name, or its address until the engine named it.
///
/// # Arguments
///
/// * `tree` - The tree.
fn root_label(tree: &CallTree) -> String {
    tree.root_name()
        .map_or_else(|| format!("{:#x}", tree.root()), str::to_owned)
}

/// Returns the label of `count` call sites.
///
/// # Arguments
///
/// * `count` - How many instructions make the call, as the engine counts them.
fn sites_label(count: usize) -> String {
    match count {
        0 => String::from("no known site"),
        1 => String::from("1 site"),
        n => format!("{n} sites"),
    }
}

/// Returns a small muted label of `text`.
///
/// # Arguments
///
/// * `text` - The label's text.
fn muted(text: impl Into<SharedString>) -> Label {
    Label::new(text).size(LabelSize::Small).color(Color::Muted)
}

/// Returns the text of a row of no node and no site.
///
/// # Arguments
///
/// * `row` - The row.
///
/// # Returns
///
/// The text, `None` for a node or site row.
fn note_of(row: &Row) -> Option<String> {
    Some(match *row {
        Row::Node { .. } | Row::Site { .. } => return None,
        Row::NoSites { .. } => String::from("The engine knows this call without its instruction"),
        Row::More { shown, total, .. } => format!("showing {shown} of {total}"),
        Row::Empty { missing, .. } => String::from(match missing {
            Missing::Callee => "The engine knows no callee of this function",
            Missing::DirectCallee => "The engine knows no direct callee of this function",
            Missing::Caller => "The engine knows no caller of this function",
        }),
        Row::Unsearched { .. } => {
            String::from("Virtual calls not searched: the function does not decompile")
        }
    })
}

/// Renders row `ix` of `tree`.
///
/// # Arguments
///
/// * `tree` - The tree.
/// * `ix` - Zero-based row index.
/// * `row` - The row at `ix`.
/// * `look` - Colors and font of the frame.
/// * `cx` - Panel context, for the row's listeners.
fn render_row(
    tree: &CallTree,
    ix: usize,
    row: &Row,
    look: &Look,
    cx: &Context<'_, CallTreePanel>,
) -> AnyElement {
    let item = ListItem::new(("call-tree-row", ix))
        .spacing(ListItemSpacing::Dense)
        .indent_level(row.depth() + 1)
        .indent_step_size(px(INDENT_PX))
        .height(px(ROW_HEIGHT_PX))
        .toggle_state(ix == tree.selected())
        .on_click(cx.listener(move |this, _, window, cx| {
            window.focus(&this.focus_handle, cx);
            this.select(ix, cx);
            this.confirm(TabMode::Preview, window, cx);
        }));
    if let Row::Site { at, .. } = *row {
        return item
            .child(
                div()
                    .font(look.font.clone())
                    .text_color(look.palette.color(Role::Address))
                    .child(format!("{at:#x}")),
            )
            .end_slot(muted("call site"))
            .into_any_element();
    }
    let Some(shape) = tree.shape(row) else {
        return item.children(note_of(row).map(muted)).into_any_element();
    };
    let edge = tree.edge(row);
    let name = edge.map_or_else(|| root_label(tree), |edge| edge.name.clone().into_string());
    let import =
        tree.direction() == Direction::Callees && edge.is_some_and(|e| e.via == Via::Import);
    let color = if import {
        look.palette.color(Role::Import)
    } else {
        look.palette.color(Role::Function)
    };
    let (toggle, note) = match shape {
        Shape::Open => (Some(true), None),
        Shape::Reading => (Some(true), Some("reading")),
        Shape::Closed => (Some(false), None),
        Shape::Leaf => (None, None),
        Shape::Cycle => (None, Some("cycle")),
    };
    let detail = edge.map(|e| format!("{}  {}", via_label(e.via), sites_label(e.site_count)));
    item.toggle(toggle)
        .always_show_disclosure_icon(true)
        .on_toggle(cx.listener(move |this, _, _, cx| this.toggle(ix, cx)))
        .child(
            div()
                .font(look.font.clone())
                .text_color(color)
                .whitespace_nowrap()
                .child(name),
        )
        .end_slot(
            h_flex()
                .gap_2()
                .children(note.map(muted))
                .children(detail.map(muted)),
        )
        .into_any_element()
}

impl Render for CallTreePanel {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let size = ThemeSettings::get_global(cx).buffer_font_size(cx);
        let root = div()
            .id("call-tree-panel")
            .key_context("CallTreePanel")
            .track_focus(&self.focus_handle)
            .size_full()
            .flex()
            .flex_col()
            .text_size(size)
            .on_action(cx.listener(|this, _: &CallTreeDirection, _, cx| this.flip_direction(cx)))
            .on_action(cx.listener(|this, _: &ToggleVirtualCalls, _, cx| {
                this.toggle_virtuals(cx);
            }))
            .on_action(cx.listener(|this, _: &ShowCallSites, _, cx| this.toggle_sites(cx)))
            .on_action(cx.listener(|this, _: &menu::Confirm, window, cx| {
                this.confirm(TabMode::Permanent, window, cx);
            }));
        if let Some(card) = self.card(cx) {
            return root.child(card.render(cx));
        }
        let Some(tree) = self.tree() else {
            return root;
        };
        let count = tree.rows().len();
        let header = header(tree);
        let list = uniform_list("call-tree", count, cx.processor(Self::render_rows))
            .track_scroll(&self.scroll)
            .with_decoration(
                indent_guides(px(INDENT_PX), IndentGuideColors::panel(cx))
                    .with_compute_indents_fn(cx.entity(), |this, range, _, _| this.depths(range)),
            )
            .flex_1()
            .min_h(px(0.0));
        root.child(header).child(list)
    }
}

impl EventEmitter<PanelEvent> for CallTreePanel {}

impl Focusable for CallTreePanel {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Panel for CallTreePanel {
    spec_panel!(PANEL);
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::name_of;
    use borer_engine::analysis::render::Level;
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use workspace::Workspace;

    use super::CallTreePanel;
    use crate::actions::{
        CallTree, CallTreeDirection, CloseBinary, ShowCallSites, ToggleVirtualCalls,
    };
    use crate::app_view::AppWindow;
    use crate::app_view::tests::{init, open, open_place};
    use crate::call_tree::tests::{MAIN, MAIN_CALLS_ZETA, MID, ZETA, tree_program};
    use crate::call_tree::{Missing, Row};
    use crate::card::Tone;
    use crate::decompile_item::{DecompileItem, Form, TabMode};
    use crate::places::Place;
    use crate::worker::{Jobs, LoadedBinary, call_level_blocking, listing_blocking};

    /// Makes `loaded` the binary open in `app`, as a finished load does, which docks the
    /// panels.
    fn load(app: &AppWindow, loaded: &Arc<LoadedBinary>, cx: &mut VisualTestContext) {
        app.binary
            .update(cx, |binary, cx| binary.show_loaded(loaded.clone(), cx));
        cx.run_until_parked();
    }

    /// Returns the workspace's call tree panel.
    fn panel_of(
        workspace: &Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> Entity<CallTreePanel> {
        workspace
            .read_with(cx, |workspace, cx| workspace.panel::<CallTreePanel>(cx))
            .unwrap()
    }

    /// Opens `entry` of `loaded` in a permanent focused tab and roots the tree there.
    fn root_at(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        entry: u64,
        cx: &mut VisualTestContext,
    ) -> Entity<CallTreePanel> {
        open_place(
            workspace,
            loaded,
            Place::decompile(entry),
            TabMode::Permanent,
            cx,
        );
        cx.run_until_parked();
        cx.dispatch_action(CallTree);
        cx.run_until_parked();
        panel_of(workspace, cx)
    }

    /// Opens a window over the tree program and roots the tree at its `main`.
    fn rooted_at_main(
        cx: &mut TestAppContext,
    ) -> (
        Entity<Workspace>,
        Arc<LoadedBinary>,
        Entity<CallTreePanel>,
        &mut VisualTestContext,
    ) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let loaded = tree_program();
        load(&app, &loaded, cx);
        let panel = root_at(&app.workspace, &loaded, MAIN, cx);
        (app.workspace, loaded, panel, cx)
    }

    /// The call tree action roots the tree at the active tab's function in the open binary
    /// and, once the background read lands, lists exactly the engine's level of it in the
    /// engine's order; the direction action lists what calls it instead, and over callers
    /// the virtual calls toggle leaves the tree as it is.
    #[gpui::test]
    fn the_tree_lists_the_engine_level_of_the_active_function(cx: &mut TestAppContext) {
        let (_, loaded, panel, cx) = rooted_at_main(cx);
        let (a, o) = (&loaded.analysis, &loaded.overlay);
        let (want, _) = call_level_blocking(&loaded, MAIN, Level::Callees);
        assert_eq!(want.rows.len(), 3);
        panel.read_with(cx, |panel, _| {
            let tree = panel.tree().unwrap();
            assert_eq!(tree.root_name(), Some(name_of(a, o, MAIN).as_str()));
            let shown: Vec<_> = tree.rows()[1..]
                .iter()
                .map(|row| tree.edge(row).cloned().unwrap())
                .collect();
            assert_eq!(shown, want.rows);
        });
        cx.dispatch_action(CallTreeDirection);
        cx.run_until_parked();
        let none = [
            Row::Node { id: 0, depth: 0 },
            Row::Empty {
                depth: 1,
                missing: Missing::Caller,
            },
        ];
        panel.read_with(cx, |panel, _| {
            let tree = panel.tree().unwrap();
            assert_eq!(tree.level(), Level::Callers);
            assert_eq!(tree.rows(), none);
        });
        cx.dispatch_action(ToggleVirtualCalls);
        cx.run_until_parked();
        panel.read_with(cx, |panel, _| {
            let tree = panel.tree().unwrap();
            assert_eq!(tree.level(), Level::Callers);
            assert_eq!(tree.rows(), none);
            assert!(tree.root_name().is_some());
        });
    }

    /// Loading another binary drops the tree rooted in the one before, and a tab of a
    /// binary no longer open roots nothing.
    #[gpui::test]
    fn a_new_binary_clears_the_tree(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        let first = tree_program();
        load(&app, &first, cx);
        let panel = root_at(&workspace, &first, MAIN, cx);
        assert!(panel.read_with(cx, |panel, _| panel.tree().is_some()));
        load(&app, &tree_program(), cx);
        assert!(panel.read_with(cx, |panel, _| panel.tree().is_none()));
        let panel = root_at(&workspace, &first, MAIN, cx);
        assert!(panel.read_with(cx, |panel, _| panel.tree().is_none()));
    }

    /// Rooting the tree again drops the reads of the tree before: each running read's
    /// cancel is raised at once, under the label naming its node, and none stays listed.
    #[gpui::test]
    fn rerooting_raises_every_running_read_cancel(cx: &mut TestAppContext) {
        let (_, loaded, panel, cx) = rooted_at_main(cx);
        let running = |cx: &mut VisualTestContext| {
            let running = cx.update(|_, cx| Jobs::running(cx));
            let labels: Vec<_> = running.iter().map(|(_, l, _)| l.to_string()).collect();
            (labels, running)
        };
        panel.update(cx, |panel, cx| panel.toggle(3, cx));
        let (labels, first) = running(cx);
        assert_eq!(labels, ["Callees of 0x1080"]);
        panel.update(cx, |panel, cx| panel.set_root(&loaded, MID, cx));
        assert!(first.iter().all(|(_, _, flag)| flag.is_raised()));
        let (labels, second) = running(cx);
        assert_eq!(labels, ["Callees of 0x1080"]);
        panel.update(cx, |panel, cx| panel.set_root(&loaded, ZETA, cx));
        assert!(second.iter().all(|(_, _, flag)| flag.is_raised()));
        assert_eq!(running(cx).0, ["Callees of 0x1040"]);
        cx.run_until_parked();
        assert!(cx.update(|_, cx| Jobs::running(cx)).is_empty());
        assert!(!panel.read_with(cx, |panel, _| panel.is_reading()));
    }

    /// With a binary open and no root the panel offers the key that roots the tree, a
    /// rooted tree draws no card, and while another binary is read the card is the
    /// binary's.
    #[gpui::test]
    fn the_panel_says_why_it_shows_no_tree(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace.clone();
        let loaded = tree_program();
        load(&app, &loaded, cx);
        let panel = panel_of(&workspace, cx);
        let card = |cx: &mut VisualTestContext| {
            panel.read_with(cx, |panel, cx| {
                panel
                    .card(cx)
                    .map(|c| (c.says.to_string(), c.tone, c.offers.len()))
            })
        };
        let says = "The tree starts at the function of the active tab".to_owned();
        assert_eq!(card(cx), Some((says, Tone::Quiet, 1)));
        root_at(&workspace, &loaded, MAIN, cx);
        assert_eq!(card(cx), None);
        let path = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        app.binary
            .update(cx, |binary, cx| binary.open_path(path, cx));
        cx.update(|_, _| ());
        let reading = "Reading borer-app-no-such-binary.exe".to_owned();
        assert_eq!(card(cx), Some((reading, Tone::Quiet, 0)));
    }

    /// Closing the binary takes the call tree out of its dock, and the next load docks one
    /// call tree again, not a second.
    #[gpui::test]
    fn a_closed_and_reopened_binary_docks_one_call_tree(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let loaded = tree_program();
        let docked = |cx: &mut VisualTestContext| {
            app.workspace.read_with(cx, |workspace, cx| {
                let docks = workspace.all_docks();
                docks
                    .iter()
                    .filter(|dock| dock.read(cx).panel::<CallTreePanel>().is_some())
                    .count()
            })
        };
        load(&app, &loaded, cx);
        assert_eq!(docked(cx), 1);
        cx.dispatch_action(CloseBinary);
        cx.run_until_parked();
        assert_eq!(docked(cx), 0);
        load(&app, &loaded, cx);
        assert_eq!(docked(cx), 1);
    }

    /// Enter on a call site opens the listing of the function making the call in a
    /// permanent tab, named for the function, with the site's line at its top as the
    /// engine's listing places it.
    #[gpui::test]
    fn enter_on_a_site_opens_the_listing_at_its_line(cx: &mut TestAppContext) {
        let (workspace, loaded, panel, cx) = rooted_at_main(cx);
        panel.update(cx, |panel, cx| panel.select(1, cx));
        cx.dispatch_action(ShowCallSites);
        let site = Row::Site {
            function: MAIN,
            at: MAIN_CALLS_ZETA,
            depth: 2,
        };
        panel.update(cx, |panel, cx| {
            let tree = panel.tree().unwrap();
            assert_eq!(tree.target(&tree.rows()[1]), Some(ZETA));
            assert_eq!(tree.rows().get(2), Some(&site));
            panel.select(2, cx);
        });
        cx.update(|window, cx| window.draw(cx).clear(cx));
        cx.dispatch_action(menu::Confirm);
        cx.run_until_parked();
        let line = listing_blocking(&loaded, MAIN)
            .unwrap()
            .line_of(MAIN_CALLS_ZETA)
            .unwrap();
        assert!(line > 0);
        let name = name_of(&loaded.analysis, &loaded.overlay, MAIN);
        cx.update(|window, cx| window.draw(cx).clear(cx));
        let shown = workspace.read_with(cx, |workspace, cx| {
            let item = workspace.active_item_as::<DecompileItem>(cx).unwrap();
            let label = workspace::Item::tab_content_text(item.read(cx), 0, cx);
            let item = item.read(cx);
            (
                item.entry(),
                item.form(),
                item.top_line(),
                label.to_string(),
            )
        });
        assert_eq!(shown, (Some(MAIN), Form::Listing, line, name));
        let preview = workspace.read_with(cx, |workspace, cx| {
            let pane = workspace.active_pane().read(cx);
            pane.preview_item_id()
        });
        let active = workspace.read_with(cx, |workspace, cx| {
            workspace.active_item(cx).map(|item| item.item_id())
        });
        assert_ne!(preview, active);
    }
}
