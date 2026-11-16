//! A graph tab: one function's control-flow graph as the engine lays it out, painted on
//! gpui's canvas (Zed has no graph widget), each block graded by the machine's check.
//!
//! The app only scales and paints: node boxes are the engine's layout times the buffer
//! font's cell, node rows are the graph's listing rows, edges follow the engine's routes.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use borer_engine::analysis::decompile::replay::{Grade, TextCheck};
use borer_engine::analysis::name_of;
use borer_engine::analysis::render::{Cfg, Cut, EdgeKind};
use gpui::{
    App, Bounds, Context, Entity, EventEmitter, FocusHandle, Focusable, Hsla,
    InteractiveElement as _, IntoElement, MouseButton, MouseDownEvent, MouseMoveEvent,
    ParentElement as _, PathBuilder, Pixels, Point, Render, ScrollEvent, SharedString, Size,
    Styled as _, TextAlign, TextRun, WeakEntity, Window, canvas, div, point, px, quad, size,
};
use settings::Settings as _;
use theme::{ActiveTheme as _, Theme};
use theme_settings::ThemeSettings;
use ui::{Icon, IconName, Label, LabelCommon as _, LabelSize, h_flex};
use workspace::{Item, Workspace};

use crate::actions::{
    BACK_HINT, FitGraph, FollowLink, ShowCheck, ShowGraph, ToggleGraph, WalkDown, WalkLeft,
    WalkRight, WalkUp, ZoomIn, ZoomOut,
};
use crate::binary::Binary;
use crate::card::{Card, Tone};
use crate::code_view::{ClickOutcome, CodePalette, Role, resolve_ref_click};
use crate::commands;
use crate::decompile_item::{DecompileItem, Form, code_row_height};
use crate::places::{Place, open_beside};
use crate::status::grade_color;
use crate::worker::{Job, LoadedBinary, check_blocking, graph_blocking};

/// Smallest and largest zoom.
const ZOOM_RANGE: (f32, f32) = (0.05, 4.0);

/// Factor one zoom step scales by.
const ZOOM_STEP: f32 = 1.25;

/// Smallest font size, in pixels, whose node text is painted; below it only boxes show.
const MIN_TEXT_PX: f32 = 3.0;

/// Width of a back edge in pixels; other edges are one pixel wide.
const BACK_EDGE_PX: f32 = 2.5;

/// Width of a node's grade strip, in pixels.
const STRIP_PX: f32 = 4.0;

/// Half the width and the length of an edge's arrow head, in pixels at zoom 1.
const ARROW_PX: (f32, f32) = (3.0, 6.0);

/// A direction an arrow key walks the graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dir {
    /// Toward the top.
    Up,
    /// Toward the bottom.
    Down,
    /// Toward the left.
    Left,
    /// Toward the right.
    Right,
}

/// Where the tab looks: the grid point at its center, in cells, and the zoom.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Camera {
    /// Grid point at the center of the tab, in cells across and rows down.
    center: Point<f32>,
    /// Pixels per pixel of the unzoomed graph.
    zoom: f32,
}

/// What the canvas painted last: its bounds, the unzoomed cell and each node box painted.
#[derive(Debug, Default)]
pub struct Painted {
    /// The canvas's bounds.
    pub bounds: Bounds<Pixels>,
    /// One text cell at zoom 1: the buffer font's advance and the code row height.
    pub cell: Size<Pixels>,
    /// Each node painted, by node index, and its box; nodes off screen are left out.
    pub nodes: Vec<(usize, Bounds<Pixels>)>,
}

/// One function's control-flow graph as an item of Zed's center pane.
pub struct GraphItem {
    /// Workspace the tab opens further places in.
    workspace: WeakEntity<Workspace>,
    /// The window's binary, whose status line the tab writes and whose load a drop starts.
    binary: Entity<Binary>,
    /// Binary the function belongs to.
    loaded: Arc<LoadedBinary>,
    /// Entry of the function.
    entry: u64,
    /// The function's name as the engine gives it, once the graph is built.
    name: Option<SharedString>,
    /// The graph, once built.
    graph: Option<Arc<Cfg>>,
    /// The engine's reason the graph was not built.
    failed: Option<String>,
    /// The check of the function's decompiled text, once run.
    check: Option<Arc<Option<TextCheck>>>,
    /// Each node's grade, by node index; empty until the check and the graph are both in.
    grades: Vec<Grade>,
    /// Index of the selected node.
    selected: usize,
    /// The address the selection was asked for, kept while the selected node holds it.
    at: Option<u64>,
    /// Where the tab looks.
    camera: Camera,
    /// Whether the selected block's evidence is shown.
    show_check: bool,
    /// What the canvas painted last.
    painted: Rc<RefCell<Painted>>,
    /// Where a drag that pans was last, while one is under way.
    drag: Option<Point<Pixels>>,
    /// The tab's focus.
    focus: FocusHandle,
    /// The background build of the graph.
    job: Job,
    /// The background check of the decompiled text.
    check_job: Job,
}

impl std::fmt::Debug for GraphItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GraphItem")
            .field("entry", &self.entry)
            .field("selected", &self.selected)
            .finish_non_exhaustive()
    }
}

impl GraphItem {
    /// Returns a tab for the graph of the function at `entry` of `loaded`, building it and
    /// the check of its text in the background.
    ///
    /// # Arguments
    ///
    /// * `workspace` - Workspace the tab opens further places in.
    /// * `binary` - The window's binary.
    /// * `loaded` - Binary the function belongs to.
    /// * `entry` - Entry virtual address of the function.
    /// * `_window` - Window the tab is in.
    /// * `cx` - Item context spawning the builds.
    #[must_use]
    pub fn new(
        workspace: WeakEntity<Workspace>,
        binary: Entity<Binary>,
        loaded: Arc<LoadedBinary>,
        entry: u64,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> Self {
        let mut item = Self {
            workspace,
            binary,
            loaded: loaded.clone(),
            entry,
            name: None,
            graph: None,
            failed: None,
            check: None,
            grades: Vec::new(),
            selected: 0,
            at: None,
            camera: Camera {
                center: point(0.0, 0.0),
                zoom: 1.0,
            },
            show_check: false,
            painted: Rc::default(),
            drag: None,
            focus: cx.focus_handle(),
            job: Job::default(),
            check_job: Job::default(),
        };
        let source = loaded.clone();
        let work = move || {
            let name = name_of(&source.analysis, &source.overlay, entry);
            (graph_blocking(&source, entry), name)
        };
        item.job.run(
            format!("Graphing {entry:#x}"),
            cx,
            work,
            |item, (graph, name), cx| {
                item.name = Some(name.into());
                match graph {
                    Ok(graph) => item.graph = Some(graph),
                    Err(why) => item.failed = Some(why),
                }
                item.regrade();
                item.select(item.at.and_then(|va| item.node_of(va)).unwrap_or(0), cx);
            },
        );
        let work = move || check_blocking(&loaded, entry);
        item.check_job.run(
            format!("Checking {entry:#x}"),
            cx,
            work,
            |item, check, cx| {
                item.check = Some(check);
                item.regrade();
                cx.notify();
            },
        );
        item
    }

    /// Returns the entry of the function the tab shows.
    #[must_use]
    pub const fn entry(&self) -> u64 {
        self.entry
    }

    /// Returns the binary the function belongs to.
    #[must_use]
    pub const fn loaded(&self) -> &Arc<LoadedBinary> {
        &self.loaded
    }

    /// Returns the graph, once built.
    #[must_use]
    pub const fn graph(&self) -> Option<&Arc<Cfg>> {
        self.graph.as_ref()
    }

    /// Returns the index of the selected node.
    #[must_use]
    pub const fn selected(&self) -> usize {
        self.selected
    }

    /// Returns what the canvas painted last.
    #[must_use]
    pub fn painted(&self) -> std::cell::Ref<'_, Painted> {
        self.painted.borrow()
    }

    /// Returns whether the graph build is still running.
    #[must_use]
    pub fn is_building(&self) -> bool {
        self.job.is_running()
    }

    /// Returns the index of the node holding the instruction at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    fn node_of(&self, va: u64) -> Option<usize> {
        let graph = self.graph.as_ref()?;
        graph.nodes.iter().position(|n| n.start <= va && va < n.end)
    }

    /// Selects the node holding the instruction at `va`, now or once the graph is built; an
    /// address no node holds selects nothing new.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    /// * `cx` - Item context.
    pub fn go_to_address(&mut self, va: u64, cx: &mut Context<'_, Self>) {
        self.at = Some(va);
        if let Some(node) = self.node_of(va) {
            self.select(node, cx);
        }
    }

    /// Selects node `node` and centers the tab on it, forgetting an asked address the node
    /// does not hold.
    ///
    /// # Arguments
    ///
    /// * `node` - Index of the node.
    /// * `cx` - Item context.
    fn select(&mut self, node: usize, cx: &mut Context<'_, Self>) {
        let Some(graph) = &self.graph else {
            return;
        };
        let drawing = graph.layout();
        if let (Some(n), Some(&(x, y)), Some(&(w, h))) = (
            graph.nodes.get(node),
            drawing.at.get(node),
            drawing.sizes.get(node),
        ) {
            self.selected = node;
            self.at = self.at.filter(|va| n.start <= *va && *va < n.end);
            let half = |v: u32| grid_u(v) / 2.0;
            self.camera.center = point(grid(x) + half(w), grid(y) + half(h));
        }
        cx.notify();
    }

    /// Recomputes each node's grade from the check, once both are in.
    fn regrade(&mut self) {
        let (Some(graph), Some(check)) = (&self.graph, &self.check) else {
            return;
        };
        self.grades = graph
            .nodes
            .iter()
            .map(|n| {
                check.as_ref().as_ref().map_or(Grade::Unchecked, |c| {
                    c.blocks
                        .binary_search_by_key(&n.start, |b| b.start())
                        .ok()
                        .and_then(|ix| c.blocks.get(ix))
                        .map_or(Grade::Unchecked, |b| b.grade())
                })
            })
            .collect();
    }

    /// Walks the selection one step in `dir` along an edge.
    ///
    /// # Arguments
    ///
    /// * `dir` - The direction.
    /// * `cx` - Item context.
    fn step(&mut self, dir: Dir, cx: &mut Context<'_, Self>) {
        if let Some(node) = self
            .graph
            .as_ref()
            .and_then(|g| walk(g, self.selected, dir))
        {
            self.select(node, cx);
        }
    }

    /// Scales the zoom by `factor`, within [`ZOOM_RANGE`].
    ///
    /// # Arguments
    ///
    /// * `factor` - The factor.
    /// * `cx` - Item context.
    fn zoom_by(&mut self, factor: f32, cx: &mut Context<'_, Self>) {
        self.camera.zoom = (self.camera.zoom * factor).clamp(ZOOM_RANGE.0, ZOOM_RANGE.1);
        cx.notify();
    }

    /// Zooms and pans so the whole drawing fits the canvas as last painted.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn fit(&mut self, cx: &mut Context<'_, Self>) {
        let Some(graph) = &self.graph else {
            return;
        };
        let (w, h) = graph.layout().size;
        let (w, h) = (grid_u(w).max(1.0), grid_u(h).max(1.0));
        let painted = self.painted.borrow();
        let (bounds, cell) = (painted.bounds.size, painted.cell);
        if cell.width > px(0.0) && cell.height > px(0.0) {
            let zoom = (bounds.width / (cell.width * w)).min(bounds.height / (cell.height * h));
            self.camera.zoom = zoom.clamp(ZOOM_RANGE.0, ZOOM_RANGE.1);
        }
        drop(painted);
        self.camera.center = point(w / 2.0, h / 2.0);
        cx.notify();
    }

    /// Pans by `delta` pixels on screen.
    ///
    /// # Arguments
    ///
    /// * `delta` - How far the content moves.
    /// * `cx` - Item context.
    fn pan(&mut self, delta: Point<Pixels>, cx: &mut Context<'_, Self>) {
        let cell = self.painted.borrow().cell;
        if cell.width > px(0.0) && cell.height > px(0.0) {
            let z = self.camera.zoom;
            self.camera.center.x -= delta.x / (cell.width * z);
            self.camera.center.y -= delta.y / (cell.height * z);
            cx.notify();
        }
    }

    /// Opens the function the first call of the selected node names, as a graph.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn follow(&self, window: &Window, cx: &mut Context<'_, Self>) {
        let Some(graph) = &self.graph else {
            return;
        };
        let Some(node) = graph.nodes.get(self.selected) else {
            return;
        };
        let view = &graph.listing;
        let callee = node.lines.clone().find_map(|row| {
            view.tokens(row)
                .find_map(|(_, _, link)| match resolve_ref_click(view, link?) {
                    ClickOutcome::OpenFunction(entry) => Some(entry),
                    ClickOutcome::ScrollToLine(_)
                    | ClickOutcome::Import(_)
                    | ClickOutcome::None => None,
                })
        });
        if let Some(entry) = callee {
            let place = Place::Graph { entry, at: None };
            open_beside(
                &self.workspace,
                &self.binary,
                &self.loaded,
                (cx.entity_id(), place),
                window,
                cx,
            );
        }
    }

    /// Opens the function's listing at the selected block, at the address asked for when
    /// the block still holds it.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the tab is in.
    /// * `cx` - Item context.
    fn toggle(&self, window: &Window, cx: &mut Context<'_, Self>) {
        let start = self
            .graph
            .as_ref()
            .and_then(|g| g.nodes.get(self.selected))
            .map(|n| n.start);
        let place = Place::Code {
            entry: self.entry,
            form: Form::Listing,
            at: self.at.or(start),
        };
        let id = cx.entity_id();
        open_beside(
            &self.workspace,
            &self.binary,
            &self.loaded,
            (id, place),
            window,
            cx,
        );
    }

    /// Returns what the tab says while it shows no graph: the engine's reason a build
    /// failed, or the build running; `None` once the graph is in.
    #[must_use]
    pub fn card(&self) -> Option<Card> {
        match (&self.graph, &self.failed) {
            (Some(_), _) => None,
            (None, Some(why)) => Some(Card {
                says: format!("Graph failed\n{why}").into(),
                tone: Tone::Error,
                offers: &[BACK_HINT],
            }),
            (None, None) => Some(Card {
                says: "Laying out the graph...".into(),
                tone: Tone::Quiet,
                offers: &[],
            }),
        }
    }

    /// Returns the evidence behind the selected block's grade, as the check spells it.
    fn evidence(&self) -> String {
        let start = self
            .graph
            .as_ref()
            .and_then(|g| g.nodes.get(self.selected))
            .map(|n| n.start);
        match (self.check.as_deref(), start) {
            (None, _) => "Checking the decompiled text...".to_owned(),
            (Some(None), _) => {
                "No check: the function does not decompile or the image has no emulator.".to_owned()
            }
            (Some(Some(check)), Some(start)) => check
                .blocks
                .iter()
                .find(|b| b.start() == start)
                .map_or_else(
                    || format!("No record of the block at {start:#x}."),
                    |b| b.spell(),
                ),
            (Some(Some(_)), None) => String::new(),
        }
    }

    /// Returns the canvas painting the graph.
    ///
    /// # Arguments
    ///
    /// * `graph` - The graph.
    /// * `cx` - Item context.
    fn canvas(&self, graph: Arc<Cfg>, cx: &App) -> impl IntoElement {
        let settings = ThemeSettings::get_global(cx);
        let frame = Frame {
            graph,
            grades: self.grades.clone(),
            selected: self.selected,
            camera: self.camera,
            colors: Colors::of(cx.theme()),
            font: settings.buffer_font.clone(),
            font_size: settings.buffer_font_size(cx),
            row: code_row_height(cx),
            painted: self.painted.clone(),
        };
        canvas(
            |_, _, _| (),
            move |bounds, (), window, cx| frame.paint(bounds, window, cx),
        )
        .size_full()
    }
}

/// Returns the node one step from `from` in `dir`: of its successors (down), predecessors
/// (up) or either (left and right), those whose center lies that way, the nearest; `None`
/// when none does.
///
/// # Arguments
///
/// * `graph` - The graph.
/// * `from` - Index of the node walked from.
/// * `dir` - The direction.
#[must_use]
pub fn walk(graph: &Cfg, from: usize, dir: Dir) -> Option<usize> {
    let drawing = graph.layout();
    let center = |n: usize| -> Option<(i64, i64)> {
        let (&(x, y), &(w, h)) = (drawing.at.get(n)?, drawing.sizes.get(n)?);
        Some((
            2 * i64::from(x) + i64::from(w),
            2 * i64::from(y) + i64::from(h),
        ))
    };
    let (fx, fy) = center(from)?;
    graph
        .edges
        .iter()
        .filter_map(|e| match (e.from == from, e.to == from, dir) {
            (true, false, Dir::Down | Dir::Left | Dir::Right) => Some(e.to),
            (false, true, Dir::Up | Dir::Left | Dir::Right) => Some(e.from),
            (true, false, Dir::Up)
            | (false, true, Dir::Down)
            | (true, true, _)
            | (false, false, _) => None,
        })
        .filter_map(|n| Some((n, center(n)?)))
        .filter_map(|(n, (x, y))| {
            let (dx, dy) = (x - fx, y - fy);
            let ahead = match dir {
                Dir::Up => -dy,
                Dir::Down => dy,
                Dir::Left => -dx,
                Dir::Right => dx,
            };
            (ahead > 0).then_some((dx.abs() + dy.abs(), n))
        })
        .min()
        .map(|(_, n)| n)
}

/// Returns what a cut graph's toolbar says, in the engine's numbers; `None` for a whole one.
///
/// # Arguments
///
/// * `cut` - What the engine left out.
#[must_use]
pub fn cut_note(cut: Option<&Cut>) -> Option<String> {
    let cut = cut?;
    let mut note = format!("showing {} of {} blocks", cut.shown, cut.total);
    if cut.edges_shown < cut.edges_total {
        note += &format!(", {} of {} edges", cut.edges_shown, cut.edges_total);
    }
    if cut.shortened > 0 {
        note += &format!(", {} blocks shortened", cut.shortened);
    }
    Some(note)
}

/// Returns the color an edge of `kind` is painted in.
///
/// Taken is the theme's success, not taken its error, a jump or fall-through muted text,
/// a switch case its info color. A back edge is drawn [`BACK_EDGE_PX`] wide in the same
/// color.
///
/// # Arguments
///
/// * `kind` - What takes the edge.
/// * `theme` - The active theme.
#[must_use]
pub fn edge_color(kind: &EdgeKind, theme: &Theme) -> Hsla {
    match kind {
        EdgeKind::Taken => theme.status().success,
        EdgeKind::NotTaken => theme.status().error,
        EdgeKind::Jump | EdgeKind::Fall => theme.colors().text_muted,
        EdgeKind::Cases(_) => theme.status().info,
    }
}

/// Returns a grid coordinate as a float.
///
/// # Arguments
///
/// * `v` - Grid lines from the drawing's origin.
#[expect(
    clippy::cast_possible_truncation,
    reason = "a grid coordinate of a capped drawing; f32 keeps it to well under a pixel"
)]
fn grid(v: i32) -> f32 {
    f64::from(v) as f32
}

/// Returns a grid size as a float.
///
/// # Arguments
///
/// * `v` - Grid cells.
#[expect(
    clippy::cast_possible_truncation,
    reason = "a grid size of a capped drawing; f32 keeps it to well under a pixel"
)]
fn grid_u(v: u32) -> f32 {
    f64::from(v) as f32
}

/// The theme colors a frame paints with.
#[derive(Debug, Clone, Copy)]
struct Colors {
    /// Token colors.
    palette: CodePalette,
    /// Plain text.
    text: Hsla,
    /// A node's fill.
    node: Hsla,
    /// A node's frame.
    border: Hsla,
    /// The selected node's frame.
    selected: Hsla,
}

impl Colors {
    /// Returns the colors of `theme`.
    ///
    /// # Arguments
    ///
    /// * `theme` - The active theme.
    fn of(theme: &Theme) -> Self {
        Self {
            palette: CodePalette::from_theme(theme),
            text: theme.colors().text,
            node: theme.colors().editor_background,
            border: theme.colors().border,
            selected: theme.colors().border_focused,
        }
    }
}

/// Everything one paint of the canvas reads, taken from the item at render.
struct Frame {
    /// The graph.
    graph: Arc<Cfg>,
    /// Each node's grade; empty until the check is in.
    grades: Vec<Grade>,
    /// Index of the selected node.
    selected: usize,
    /// Where the tab looks.
    camera: Camera,
    /// The colors.
    colors: Colors,
    /// The buffer font.
    font: gpui::Font,
    /// The buffer font size at zoom 1.
    font_size: Pixels,
    /// The code row height at zoom 1.
    row: Pixels,
    /// Where the paint records what it painted.
    painted: Rc<RefCell<Painted>>,
}

impl Frame {
    /// Paints the nodes and edges that meet `bounds`, and records them.
    ///
    /// # Arguments
    ///
    /// * `bounds` - The canvas.
    /// * `window` - Window painted.
    /// * `cx` - Application context.
    fn paint(self, bounds: Bounds<Pixels>, window: &mut Window, cx: &mut App) {
        let font_id = window.text_system().resolve_font(&self.font);
        let advance = window.text_system().ch_advance(font_id, self.font_size);
        let cell = size(advance.unwrap_or(self.row / 2.0), self.row);
        let z = self.camera.zoom;
        let zoomed = size(cell.width * z, cell.height * z);
        let at = |x: f32, y: f32| {
            bounds.center()
                + point(
                    zoomed.width * (x - self.camera.center.x),
                    zoomed.height * (y - self.camera.center.y),
                )
        };
        let drawing = self.graph.layout();
        let theme = cx.theme().clone();
        for (edge, route) in self.graph.edges.iter().zip(&drawing.routes) {
            let points: Vec<_> = route.iter().map(|&(x, y)| at(grid(x), grid(y))).collect();
            let (Some(first), Some(last)) = (points.first(), points.last()) else {
                continue;
            };
            let reach = points
                .iter()
                .fold(Bounds::new(*first, size(px(0.0), px(0.0))), |b, p| {
                    b.union(&Bounds::new(*p, size(px(1.0), px(1.0))))
                });
            if !reach.intersects(&bounds) {
                continue;
            }
            let color = edge_color(&edge.kind, &theme);
            let width = if edge.back { BACK_EDGE_PX } else { 1.0 };
            let mut line = PathBuilder::stroke(px(width));
            line.move_to(*first);
            for p in points.iter().skip(1) {
                line.line_to(*p);
            }
            let mut head = PathBuilder::fill();
            let (half, long) = (px(ARROW_PX.0 * z.min(1.0)), px(ARROW_PX.1 * z.min(1.0)));
            head.move_to(*last);
            head.line_to(*last - point(half, long));
            head.line_to(*last + point(half, -long));
            head.close();
            for path in [line.build(), head.build()].into_iter().flatten() {
                window.paint_path(path, color);
            }
        }
        let mut painted = Vec::new();
        let font_size = self.font_size * z;
        for (ix, node) in self.graph.nodes.iter().enumerate() {
            let (Some(&(x, y)), Some(&(w, h))) = (drawing.at.get(ix), drawing.sizes.get(ix)) else {
                continue;
            };
            let rect = Bounds::new(
                at(grid(x), grid(y)),
                size(zoomed.width * grid_u(w), zoomed.height * grid_u(h)),
            );
            if !rect.intersects(&bounds) {
                continue;
            }
            painted.push((ix, rect));
            let chosen = ix == self.selected;
            let (frame, frame_px) = if chosen {
                (self.colors.selected, 2.0)
            } else {
                (self.colors.border, 1.0)
            };
            window.paint_quad(quad(
                rect,
                px(0.0),
                self.colors.node,
                px(frame_px),
                frame,
                gpui::BorderStyle::Solid,
            ));
            let grade = self.grades.get(ix).copied().unwrap_or_default();
            let strip = Bounds::new(rect.origin, size(px(STRIP_PX), rect.size.height));
            window.paint_quad(gpui::fill(strip, grade_color(grade, &theme)));
            if font_size < px(MIN_TEXT_PX) {
                continue;
            }
            for (k, row) in node.lines.clone().enumerate() {
                let top = rect.origin.y
                    + zoomed.height * (grid_u(1) + grid_u(k.try_into().unwrap_or(u32::MAX)));
                if top > bounds.bottom() || top + zoomed.height < bounds.top() {
                    continue;
                }
                self.paint_row(
                    row,
                    point(rect.origin.x + zoomed.width, top),
                    (font_size, zoomed.height),
                    window,
                    cx,
                );
            }
        }
        *self.painted.borrow_mut() = Painted {
            bounds,
            cell,
            nodes: painted,
        };
    }

    /// Paints row `row` of the graph's listing at `origin`, each token in its role's color.
    ///
    /// # Arguments
    ///
    /// * `row` - The listing row.
    /// * `origin` - Top left of the row.
    /// * `(font_size, height)` - Zoomed font size and row height.
    /// * `window` - Window painted.
    /// * `cx` - Application context.
    fn paint_row(
        &self,
        row: usize,
        origin: Point<Pixels>,
        (font_size, height): (Pixels, Pixels),
        window: &mut Window,
        cx: &mut App,
    ) {
        let view = &self.graph.listing;
        let Some(text) = view.line(row) else {
            return;
        };
        let runs: Vec<TextRun> = view
            .tokens(row)
            .map(|(span, kind, link)| TextRun {
                len: span.len(),
                font: self.font.clone(),
                color: Role::of(kind, link)
                    .map_or(self.colors.text, |r| self.colors.palette.color(r)),
                background_color: None,
                underline: None,
                strikethrough: None,
            })
            .collect();
        let shaped = window.text_system().shape_line(
            SharedString::from(text.to_owned()),
            font_size,
            &runs,
            None,
        );
        shaped
            .paint(origin, height, TextAlign::Left, None, window, cx)
            .unwrap_or(());
    }
}

/// Registers the graph's actions on `workspace`, over the window's `binary`.
///
/// Show and toggle open the active code tab's graph; the rest act on the active graph
/// tab, so the command palette offers them wherever focus is.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    /// Registers `action` to run `act` on the active graph tab.
    fn on<A: gpui::Action>(
        workspace: &mut Workspace,
        binary: &Entity<Binary>,
        act: impl Fn(&mut GraphItem, &mut Context<'_, GraphItem>) + 'static,
    ) {
        commands::register(workspace, binary, move |workspace, _: &A, _, cx| {
            if let Some(item) = workspace.active_item_as::<GraphItem>(cx) {
                item.update(cx, |item, cx| act(item, cx));
            }
        });
    }
    /// Registers `action` to switch the active code tab to its function's graph.
    fn on_code<A: gpui::Action>(workspace: &mut Workspace, binary: &Entity<Binary>) {
        commands::register(workspace, binary, |workspace, _: &A, window, cx| {
            if let Some(item) = workspace.active_item_as::<DecompileItem>(cx) {
                item.update(cx, |item, cx| item.toggle_graph(window, cx));
            }
        });
    }
    on_code::<ShowGraph>(workspace, binary);
    on_code::<ToggleGraph>(workspace, binary);
    on::<ZoomIn>(workspace, binary, |item, cx| item.zoom_by(ZOOM_STEP, cx));
    on::<ZoomOut>(workspace, binary, |item, cx| {
        item.zoom_by(1.0 / ZOOM_STEP, cx);
    });
    on::<FitGraph>(workspace, binary, GraphItem::fit);
    on::<WalkUp>(workspace, binary, |item, cx| item.step(Dir::Up, cx));
    on::<WalkDown>(workspace, binary, |item, cx| item.step(Dir::Down, cx));
    on::<WalkLeft>(workspace, binary, |item, cx| item.step(Dir::Left, cx));
    on::<WalkRight>(workspace, binary, |item, cx| item.step(Dir::Right, cx));
    on::<ShowCheck>(workspace, binary, |item, cx| {
        item.show_check = !item.show_check;
        cx.notify();
    });
}

impl EventEmitter<()> for GraphItem {}

impl Focusable for GraphItem {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Item for GraphItem {
    type Event = ();

    fn tab_content_text(&self, _detail: usize, _cx: &App) -> SharedString {
        self.name
            .clone()
            .unwrap_or_else(|| format!("{:#x}", self.entry).into())
    }

    fn tab_icon(&self, _window: &Window, _cx: &App) -> Option<Icon> {
        Some(Icon::new(IconName::GitBranch))
    }

    crate::app_view::snapshot_tab!();
}

impl Render for GraphItem {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let root = div()
            .key_context("GraphView")
            .track_focus(&self.focus)
            .size_full()
            .flex()
            .flex_col()
            .on_action(cx.listener(|this, _: &ToggleGraph, window, cx| this.toggle(window, cx)))
            .on_action(cx.listener(|this, _: &FollowLink, window, cx| this.follow(window, cx)));
        let Some(graph) = self.graph.clone() else {
            return root.children(self.card().map(|card| card.render(cx)));
        };
        let toolbar = h_flex()
            .gap_2()
            .px_2()
            .child(Label::new(self.tab_content_text(0, cx)).buffer_font(cx))
            .children(cut_note(graph.cut.as_ref()).map(|note| {
                Label::new(note)
                    .size(LabelSize::Small)
                    .color(ui::Color::Warning)
            }));
        let body = div()
            .flex_1()
            .overflow_hidden()
            .on_mouse_down(
                MouseButton::Left,
                cx.listener(|this, event: &MouseDownEvent, window, cx| {
                    this.drag = Some(event.position);
                    window.focus(&this.focus, cx);
                    let hit = this
                        .painted
                        .borrow()
                        .nodes
                        .iter()
                        .find(|(_, rect)| rect.contains(&event.position))
                        .map(|&(ix, _)| ix);
                    if let Some(ix) = hit {
                        this.selected = ix;
                        this.at = None;
                        cx.notify();
                    }
                }),
            )
            .on_mouse_move(cx.listener(|this, event: &MouseMoveEvent, _, cx| {
                match (this.drag, event.pressed_button) {
                    (Some(from), Some(MouseButton::Left)) => {
                        this.drag = Some(event.position);
                        this.pan(event.position - from, cx);
                    }
                    _ => this.drag = None,
                }
            }))
            .on_scroll(cx.listener(|this, event: &ScrollEvent, _, cx| {
                let delta = event.delta.pixel_delta(code_row_height(cx));
                if event.modifiers.secondary(cx) {
                    let factor = if delta.y > px(0.0) {
                        ZOOM_STEP
                    } else {
                        1.0 / ZOOM_STEP
                    };
                    this.zoom_by(factor, cx);
                } else {
                    this.pan(delta, cx);
                }
            }))
            .child(self.canvas(graph, cx));
        let evidence = self.show_check.then(|| {
            div()
                .p_2()
                .border_t_1()
                .border_color(cx.theme().colors().border)
                .child(
                    Label::new(self.evidence())
                        .size(LabelSize::Small)
                        .buffer_font(cx),
                )
        });
        root.child(toolbar).child(body).children(evidence)
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use crate::app_settings::BORER_THEME;
    use borer_engine::analysis::BlockTerm;
    use borer_engine::analysis::decompile::replay::Grade;
    use borer_engine::analysis::render::{Cut, EdgeKind};
    use gpui::{Entity, TestAppContext, VisualTestContext, point, px, size};
    use workspace::Workspace;

    use super::{Dir, GraphItem, cut_note, edge_color, grade_color, grid, grid_u, walk};
    use crate::app_view::tests::{CALLER, init, open, open_place, sample};
    use crate::decompile_item::tests::{active, fourth_instruction};
    use crate::decompile_item::{Form, TabMode};
    use crate::places::Place;
    use crate::worker::{LoadedBinary, Sources, graph_blocking, load_binary_blocking};

    /// Most functions of the test executable whose graphs are walked.
    const WALKED: usize = 300;

    /// Opens `place`, lets the builds settle and a frame paint, and returns the graph tab.
    fn open_graph(
        workspace: &Entity<Workspace>,
        loaded: &Arc<LoadedBinary>,
        place: Place,
        cx: &mut VisualTestContext,
    ) -> Entity<GraphItem> {
        open_place(workspace, loaded, place, TabMode::Preview, cx);
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
        workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<GraphItem>(cx)
            })
            .unwrap()
    }

    /// Each painted node box is the engine's layout times the cell: its size the drawn size
    /// in cells, its offset from the entry node's box the difference of their places.
    #[gpui::test]
    fn painted_nodes_are_the_engines_layout_scaled(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let loaded = sample();
        let place = Place::Graph {
            entry: CALLER,
            at: None,
        };
        let tab = open_graph(&workspace, &loaded, place, cx);
        tab.read_with(cx, |item, _| {
            let graph = item.graph().unwrap();
            let drawing = graph.layout();
            let painted = item.painted();
            let cell = painted.cell;
            assert_eq!(painted.nodes.len(), graph.nodes.len());
            let (_, first) = painted.nodes[0];
            for &(ix, rect) in &painted.nodes {
                let (x, y) = drawing.at[ix];
                let (x0, y0) = drawing.at[painted.nodes[0].0];
                let (w, h) = drawing.sizes[ix];
                let want = point(
                    cell.width * (grid(x) - grid(x0)),
                    cell.height * (grid(y) - grid(y0)),
                );
                let near = |a: gpui::Pixels, b: gpui::Pixels| (a - b).abs() < px(0.01);
                let off = rect.origin - first.origin;
                assert!(near(off.x, want.x) && near(off.y, want.y), "node {ix}");
                let want = size(cell.width * grid_u(w), cell.height * grid_u(h));
                assert!(near(rect.size.width, want.width), "node {ix}");
                assert!(near(rect.size.height, want.height), "node {ix}");
            }
            let rows: usize = graph.nodes.iter().map(|n| n.lines.len()).sum();
            assert!(
                rows > 0
                    && graph
                        .nodes
                        .iter()
                        .all(|n| n.lines.end <= graph.listing.lines())
            );
        });
    }

    /// Every arrow from every node, a conditional one's included, reaches only nodes an edge
    /// joins to it, over the first functions of the test executable.
    #[test]
    fn arrows_walk_only_along_edges() {
        let exe = std::env::current_exe().unwrap();
        let loaded = load_binary_blocking(exe, &Sources::default(), Vec::new()).unwrap();
        let (mut conds, mut steps) = (0, 0);
        for row in loaded.initial_rows.rows.iter().take(WALKED) {
            let Ok(graph) = graph_blocking(&loaded, row.entry) else {
                continue;
            };
            for (ix, node) in graph.nodes.iter().enumerate() {
                conds += usize::from(node.term == BlockTerm::Cond);
                for dir in [Dir::Up, Dir::Down, Dir::Left, Dir::Right] {
                    let Some(to) = walk(&graph, ix, dir) else {
                        continue;
                    };
                    steps += 1;
                    let joined = graph
                        .edges
                        .iter()
                        .any(|e| (e.from == ix && e.to == to) || (e.to == ix && e.from == to));
                    assert!(joined, "{:#x}: {ix} {dir:?} to {to}", row.entry);
                    if dir == Dir::Down && node.term == BlockTerm::Cond {
                        assert!(graph.edges.iter().any(|e| e.from == ix && e.to == to));
                    }
                }
            }
        }
        assert!(conds > 0 && steps > 0);
    }

    /// Space from the listing at a line selects the block holding that line's instruction,
    /// and Space again comes back to that line.
    #[gpui::test]
    fn space_toggles_listing_and_graph_at_one_address(cx: &mut TestAppContext) {
        let loaded = sample();
        let (va, line) = fourth_instruction(&loaded);
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let place = Place::Code {
            entry: CALLER,
            form: Form::Listing,
            at: Some(va),
        };
        open_place(&workspace, &loaded, place, TabMode::Permanent, cx);
        assert_eq!(active(&workspace, cx), Some((CALLER, Form::Listing, line)));
        cx.simulate_keystrokes("space");
        cx.run_until_parked();
        let tab = workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<GraphItem>(cx)
            })
            .unwrap();
        tab.read_with(cx, |item, _| {
            let node = &item.graph().unwrap().nodes[item.selected()];
            assert!(node.start <= va && va < node.end);
        });
        cx.update(|window, cx| window.draw(cx).clear(cx));
        cx.simulate_keystrokes("space");
        assert_eq!(active(&workspace, cx), Some((CALLER, Form::Listing, line)));
    }

    /// Every edge kind and every grade has a theme color, the kinds and grades a person
    /// tells apart each their own.
    #[test]
    fn every_edge_kind_and_grade_has_a_theme_color() {
        let family = theme_settings::deserialize_user_theme(BORER_THEME).unwrap();
        for content in &family.themes {
            let theme = &theme_settings::refine_theme(content);
            let kinds = [
                EdgeKind::Taken,
                EdgeKind::NotTaken,
                EdgeKind::Jump,
                EdgeKind::Fall,
                EdgeKind::Cases(vec![0]),
            ];
            let edges: Vec<_> = kinds.iter().map(|k| edge_color(k, theme)).collect();
            assert_eq!(edges[2], edges[3]);
            for (i, j) in [(0, 1), (0, 2), (0, 4), (1, 2), (1, 4), (2, 4)] {
                assert_ne!(edges[i], edges[j], "{:?} and {:?}", kinds[i], kinds[j]);
            }
            let grades = [Grade::Proved, Grade::Tested, Grade::Wrong, Grade::Unchecked];
            let colors: Vec<_> = grades.iter().map(|g| grade_color(*g, theme)).collect();
            for i in 0..colors.len() {
                for j in i + 1..colors.len() {
                    assert_ne!(colors[i], colors[j], "{:?} and {:?}", grades[i], grades[j]);
                }
            }
        }
    }

    /// A cut graph says the engine's counts; a whole one says nothing.
    #[test]
    fn a_cut_graph_says_the_engines_counts() {
        let cut = Cut {
            shown: 2048,
            total: 5000,
            edges_shown: 8192,
            edges_total: 9000,
            shortened: 3,
        };
        assert_eq!(
            cut_note(Some(&cut)).as_deref(),
            Some("showing 2048 of 5000 blocks, 8192 of 9000 edges, 3 blocks shortened")
        );
        assert_eq!(cut_note(None), None);
    }
}
