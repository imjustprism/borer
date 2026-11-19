//! The status bar's items beside the facts line ([`crate::binary::StatusLine`]).
//!
//! They are the engine's check grades of the function in the active tab, the running load
//! with its cancel, the active function's address, the light and dark switch and the
//! palette's key.
//!
//! Each formats what the engine or the binary holds and derives nothing; the grades come
//! from a background engine call, never from the UI thread.

use std::sync::Arc;
use std::time::{Duration, Instant};

use borer_engine::analysis::decompile::replay::{Grade, TextCheck};
use gpui::{
    Action, AnyElement, App, AppContext as _, Context, Entity, Hsla, InteractiveElement as _,
    IntoElement, ParentElement as _, Render, StatefulInteractiveElement as _, Styled as _,
    Subscription, Task, Window, div, px,
};
use theme::{ActiveTheme as _, Theme};
use ui::{
    ButtonCommon as _, Clickable as _, Color, IconButton, IconName, IconSize, KeyBinding,
    LabelCommon as _, Tooltip, h_flex,
};
use workspace::{HideStatusItem, ItemHandle, StatusItemView};

use crate::actions::{PALETTE_HINT, ToggleTheme};
use crate::app_assets::{AppIcon, Glyph};
use crate::binary::{Binary, Loading, reading_label, status_label};
use crate::check_marks::GRADE_COUNT;
use crate::decompile_item::DecompileItem;
use crate::worker::{GradeCounts, Job, LoadedBinary, grade_counts_blocking};

/// How long a load runs before the work item shows it.
const WORK_SHOWN_AFTER: Duration = Duration::from_millis(100);

/// How often the work item redraws its elapsed time, in whole seconds, while it shows.
const WORK_TICK: Duration = Duration::from_secs(1);

/// Width in logical pixels of a grade's rail.
const RAIL_WIDTH_PX: f32 = 4.0;

/// Height in logical pixels of a grade's rail.
const RAIL_HEIGHT_PX: f32 = 11.0;

/// Returns the decompile tab `item` is, when it shows a function.
///
/// # Arguments
///
/// * `item` - The active item of the active pane, if any.
/// * `cx` - Application context reading the tab.
fn function_tab(item: Option<&dyn ItemHandle>, cx: &App) -> Option<Entity<DecompileItem>> {
    item?
        .downcast::<DecompileItem>()
        .filter(|tab| tab.read(cx).entry().is_some())
}

/// The function a check is for: the binary, by identity, the entry, and the check rechecks
/// left in the session, by identity.
#[derive(Debug, Clone)]
struct Checked {
    /// The binary the tab's function belongs to.
    loaded: Arc<LoadedBinary>,
    /// The function's entry.
    entry: u64,
    /// The function's check as rechecks left it ([`Binary::rechecked`]), `None` when no
    /// recheck changed it.
    rechecked: Option<Arc<Option<TextCheck>>>,
}

impl Checked {
    /// Returns whether `other` is the same function of the same loaded binary, under the
    /// same rechecks.
    ///
    /// # Arguments
    ///
    /// * `other` - Another function.
    fn is(&self, other: &Self) -> bool {
        let same = match (&self.rechecked, &other.rechecked) {
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            (None, None) => true,
            (Some(_), None) | (None, Some(_)) => false,
        };
        Arc::ptr_eq(&self.loaded, &other.loaded) && self.entry == other.entry && same
    }
}

/// The grades of the function in the active tab, in the order the bar shows them.
const SHOWN_GRADES: [Grade; GRADE_COUNT] =
    [Grade::Proved, Grade::Tested, Grade::Unchecked, Grade::Wrong];

/// Returns the theme's syntax key of `grade` and the words the engine's header line counts
/// it with.
///
/// # Arguments
///
/// * `grade` - The engine's grade.
const fn grade_words(grade: Grade) -> (&'static str, &'static str) {
    match grade {
        Grade::Proved => ("borer.grade.proved", "proved vs lift"),
        Grade::Tested => ("borer.grade.tested", "tested"),
        Grade::Unchecked => ("borer.grade.unchecked", "unknown"),
        Grade::Wrong => ("borer.grade.wrong", "disagree"),
    }
}

/// Returns what the bar says of `grade` in `counts`.
///
/// # Arguments
///
/// * `counts` - What the check found.
/// * `grade` - The grade.
#[must_use]
pub fn grade_text(counts: &GradeCounts, grade: Grade) -> String {
    format!("{} {}", counts.count(grade), grade_words(grade).1)
}

/// The block grades the engine's check gave the function in the active tab.
pub struct Grades {
    /// The function the last check answered for, and its counts, `None` inside when the
    /// engine had no check of it; kept so the same function is not checked again.
    shown: Option<(Checked, Option<GradeCounts>)>,
    /// The function the running check is for.
    running: Option<Checked>,
    /// The tab followed, and the observer that rechecks when it changes function.
    tab: Option<(Entity<DecompileItem>, Subscription)>,
    /// The running background check.
    job: Job,
    /// The window's binary, whose session holds the rechecked checks.
    binary: Entity<Binary>,
}

impl std::fmt::Debug for Grades {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Grades")
            .field("shown", &self.shown())
            .finish_non_exhaustive()
    }
}

impl Grades {
    /// Returns the item, showing nothing until a function tab is active.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary.
    #[must_use]
    pub fn new(binary: Entity<Binary>) -> Self {
        Self {
            shown: None,
            running: None,
            tab: None,
            job: Job::default(),
            binary,
        }
    }

    /// Returns the entry of the function the counts are for and the counts, once the check
    /// answered.
    #[must_use]
    pub fn shown(&self) -> Option<(u64, GradeCounts)> {
        self.shown
            .as_ref()
            .and_then(|(checked, counts)| counts.map(|counts| (checked.entry, counts)))
    }

    /// Returns the generation of the latest check started.
    #[must_use]
    pub const fn ticket(&self) -> u64 {
        self.job.ticket()
    }

    /// Checks the function the followed tab shows in the background, unless its counts
    /// are shown or its check runs already; with no tab, cancels any check and shows
    /// nothing.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn request(&mut self, cx: &mut Context<'_, Self>) {
        let target = self.tab.as_ref().and_then(|(tab, _)| {
            let tab = tab.read(cx);
            let entry = tab.entry()?;
            let rechecked = self.binary.read(cx).rechecked(&tab.loaded().state(), entry);
            Some(Checked {
                loaded: tab.loaded().clone(),
                entry,
                rechecked,
            })
        });
        let Some(target) = target else {
            self.job.stop();
            self.running = None;
            self.shown = None;
            cx.notify();
            return;
        };
        let shown = self
            .shown
            .as_ref()
            .is_some_and(|(shown, _)| shown.is(&target));
        let running = self
            .running
            .as_ref()
            .is_some_and(|running| running.is(&target));
        if shown || running {
            return;
        }
        self.shown = None;
        self.running = Some(target.clone());
        cx.notify();
        let job = target.clone();
        let work = move || match &job.rechecked {
            Some(check) => check.as_ref().as_ref().map(GradeCounts::of),
            None => grade_counts_blocking(&job.loaded, job.entry),
        };
        let label = format!("Grading {:#x}", target.entry);
        self.job.run(label, cx, work, |grades, counts, cx| {
            grades.running = None;
            grades.shown = Some((target, counts));
            cx.notify();
        });
    }
}

/// Returns the theme's color for `grade`, under its `borer.grade.*` syntax key, the muted
/// text color when the theme has none.
///
/// # Arguments
///
/// * `grade` - The engine's grade.
/// * `theme` - The theme.
#[must_use]
pub fn grade_color(grade: Grade, theme: &Theme) -> Hsla {
    let (key, _) = grade_words(grade);
    theme
        .syntax()
        .style_for_name(key)
        .and_then(|style| style.color)
        .unwrap_or(theme.colors().text_muted)
}

impl Render for Grades {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let Some((_, counts)) = self.shown() else {
            return div().into_any_element();
        };
        let cells = SHOWN_GRADES.into_iter().map(|grade| {
            let color = match grade {
                Grade::Wrong if counts.disagree > 0 => Color::Error,
                Grade::Proved | Grade::Tested | Grade::Unchecked | Grade::Wrong => Color::Muted,
            };
            h_flex()
                .gap(px(5.0))
                .child(
                    div()
                        .w(px(RAIL_WIDTH_PX))
                        .h(px(RAIL_HEIGHT_PX))
                        .bg(grade_color(grade, cx.theme())),
                )
                .child(status_label(grade_text(&counts, grade), color))
        });
        h_flex().gap(px(12.0)).children(cells).into_any_element()
    }
}

impl StatusItemView for Grades {
    fn set_active_pane_item(
        &mut self,
        active_pane_item: Option<&dyn ItemHandle>,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.tab = function_tab(active_pane_item, cx).map(|tab| {
            let observe = cx.observe(&tab, |grades: &mut Self, _, cx| grades.request(cx));
            (tab, observe)
        });
        self.request(cx);
    }

    fn hide_setting(&self, _cx: &App) -> Option<HideStatusItem> {
        None
    }
}

/// The running load: what it reads, for how long, and a button that cancels it.
pub struct Work {
    /// The window's binary.
    binary: Entity<Binary>,
    /// The load the redraw task follows, by its start.
    ticking_for: Option<Instant>,
    /// Redraws the elapsed time while the load runs.
    tick: Option<Task<()>>,
    /// Follows the binary's loads.
    _observe: Subscription,
}

impl std::fmt::Debug for Work {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Work").finish_non_exhaustive()
    }
}

impl Work {
    /// Returns the work item of `binary`.
    ///
    /// # Arguments
    ///
    /// * `binary` - The window's binary.
    /// * `cx` - Item context.
    #[must_use]
    pub fn new(binary: Entity<Binary>, cx: &mut Context<'_, Self>) -> Self {
        let observe = cx.observe(&binary, |work: &mut Self, _, cx| work.follow(cx));
        let mut work = Self {
            binary,
            ticking_for: None,
            tick: None,
            _observe: observe,
        };
        work.follow(cx);
        work
    }

    /// Starts redrawing for a load that started since the last one, once when the item
    /// shows ([`WORK_SHOWN_AFTER`]) and every [`WORK_TICK`] after, until that load ends.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    fn follow(&mut self, cx: &mut Context<'_, Self>) {
        cx.notify();
        let Some(since) = self.binary.read(cx).reading().map(|loading| loading.since) else {
            return;
        };
        if self.ticking_for == Some(since) {
            return;
        }
        self.ticking_for = Some(since);
        self.tick = Some(cx.spawn(async move |this, cx| {
            let mut wait = WORK_SHOWN_AFTER;
            loop {
                cx.background_executor().timer(wait).await;
                wait = WORK_TICK;
                let Some(this) = this.upgrade() else {
                    return;
                };
                let running = this.update(cx, |work, cx| {
                    cx.notify();
                    work.binary
                        .read(cx)
                        .reading()
                        .is_some_and(|loading| loading.since == since)
                });
                if !running {
                    return;
                }
            }
        }));
    }
}

/// Returns how long `loading` has run at `now` once the work item shows it, `None` before
/// [`WORK_SHOWN_AFTER`].
///
/// # Arguments
///
/// * `loading` - The running load.
/// * `now` - The executor's clock.
#[must_use]
pub fn shown_for(loading: &Loading, now: Instant) -> Option<Duration> {
    let elapsed = now.saturating_duration_since(loading.since);
    (elapsed >= WORK_SHOWN_AFTER).then_some(elapsed)
}

impl Render for Work {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let Some(loading) = self.binary.read(cx).reading() else {
            return div().into_any_element();
        };
        let now = cx.background_executor().now();
        let Some(elapsed) = shown_for(loading, now) else {
            return div().into_any_element();
        };
        let label = reading_label(&loading.path);
        let binary = self.binary.clone();
        h_flex()
            .gap(px(8.0))
            .child(status_label(label, Color::Muted))
            .child(status_label(
                format!("{} s", elapsed.as_secs()),
                Color::Placeholder,
            ))
            .child(
                IconButton::new("cancel-load", IconName::Close)
                    .icon_size(IconSize::XSmall)
                    .icon_color(Color::Placeholder)
                    .tooltip(Tooltip::text("Cancel"))
                    .on_click(move |_, _, cx| {
                        binary.update(cx, |binary, cx| binary.cancel_load(cx));
                    }),
            )
            .into_any_element()
    }
}

impl StatusItemView for Work {
    fn set_active_pane_item(
        &mut self,
        _active_pane_item: Option<&dyn ItemHandle>,
        _window: &mut Window,
        _cx: &mut Context<'_, Self>,
    ) {
    }

    fn hide_setting(&self, _cx: &App) -> Option<HideStatusItem> {
        None
    }
}

/// The entry address of the function in the active tab; it becomes the cursor's address
/// once code views have a cursor.
#[derive(Debug, Default)]
pub struct Address {
    /// The tab followed, and the observer that redraws when it changes function.
    tab: Option<(Entity<DecompileItem>, Subscription)>,
}

impl Address {
    /// Returns the address shown, if any.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the tab.
    #[must_use]
    pub fn shown(&self, cx: &App) -> Option<u64> {
        self.tab.as_ref().and_then(|(tab, _)| tab.read(cx).entry())
    }
}

impl Render for Address {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let Some(address) = self.shown(cx) else {
            return div().into_any_element();
        };
        status_label(format!("{address:#x}"), Color::Hint)
            .buffer_font(cx)
            .into_any_element()
    }
}

impl StatusItemView for Address {
    fn set_active_pane_item(
        &mut self,
        active_pane_item: Option<&dyn ItemHandle>,
        _window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.tab = function_tab(active_pane_item, cx).map(|tab| {
            let observe = cx.observe(&tab, |_: &mut Self, _, cx| cx.notify());
            (tab, observe)
        });
        cx.notify();
    }

    fn hide_setting(&self, _cx: &App) -> Option<HideStatusItem> {
        None
    }
}

/// A control that runs `action` on a click, with a tooltip naming it and its key.
///
/// # Arguments
///
/// * `id` - Element id.
/// * `title` - What the tooltip calls the action.
/// * `action` - The action.
/// * `child` - What the control shows.
/// * `cx` - Application context reading the theme.
fn action_control(
    id: &'static str,
    title: &'static str,
    action: &dyn Action,
    child: AnyElement,
    cx: &App,
) -> AnyElement {
    let hover = cx.theme().colors().ghost_element_hover;
    let run = action.boxed_clone();
    div()
        .id(id)
        .px(px(4.0))
        .rounded(px(4.0))
        .flex()
        .items_center()
        .gap(px(6.0))
        .cursor_pointer()
        .hover(move |cell| cell.bg(hover))
        .tooltip(Tooltip::for_action_title(title, action))
        .on_click(move |_, window, cx| window.dispatch_action(run.boxed_clone(), cx))
        .child(child)
        .into_any_element()
}

/// The light and dark switch.
#[derive(Debug, Default)]
pub struct ThemeSwitch;

impl Render for ThemeSwitch {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let icon = Glyph::App(AppIcon::Theme)
            .icon()
            .size(IconSize::Small)
            .color(Color::Muted);
        action_control(
            "theme-switch",
            "Toggle Light and Dark",
            &ToggleTheme,
            icon.into_any_element(),
            cx,
        )
    }
}

impl StatusItemView for ThemeSwitch {
    fn set_active_pane_item(
        &mut self,
        _active_pane_item: Option<&dyn ItemHandle>,
        _window: &mut Window,
        _cx: &mut Context<'_, Self>,
    ) {
    }

    fn hide_setting(&self, _cx: &App) -> Option<HideStatusItem> {
        None
    }
}

/// The command palette's name and key.
#[derive(Debug, Default)]
pub struct PaletteHint;

impl Render for PaletteHint {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let (toggle, _) = PALETTE_HINT;
        let child = h_flex()
            .gap(px(6.0))
            .child(status_label("palette", Color::Muted))
            .child(KeyBinding::for_action(toggle, cx))
            .into_any_element();
        action_control("palette", "Command Palette", toggle, child, cx)
    }
}

impl StatusItemView for PaletteHint {
    fn set_active_pane_item(
        &mut self,
        _active_pane_item: Option<&dyn ItemHandle>,
        _window: &mut Window,
        _cx: &mut Context<'_, Self>,
    ) {
    }

    fn hide_setting(&self, _cx: &App) -> Option<HideStatusItem> {
        None
    }
}

/// Adds the status items to `workspace`'s status bar beside the facts line, in the order
/// the bar shows them: grades and work on the left, then address, theme and palette on
/// the right.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn add_items(
    workspace: &mut workspace::Workspace,
    binary: &Entity<Binary>,
    window: &mut Window,
    cx: &mut Context<'_, workspace::Workspace>,
) {
    let grades = cx.new(|_| Grades::new(binary.clone()));
    let work = cx.new(|cx| Work::new(binary.clone(), cx));
    let address = cx.new(|_| Address::default());
    let theme = cx.new(|_| ThemeSwitch);
    let palette = cx.new(|_| PaletteHint);
    workspace.status_bar().update(cx, |bar, cx| {
        bar.add_left_item(grades, window, cx);
        bar.add_left_item(work, window, cx);
        bar.add_right_item(palette, window, cx);
        bar.add_right_item(theme, window, cx);
        bar.add_right_item(address, window, cx);
    });
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::path::PathBuf;
    use std::rc::Rc;
    use std::sync::Arc;
    use std::time::Duration;

    use borer_engine::analysis::decompile::Site;
    use borer_engine::analysis::decompile::replay::{BlockCheck, Grade, TextCheck};
    use borer_engine::analysis::decompile::text_check;
    use borer_engine::analysis::render::{
        Budget, FunctionOrder, Repair, answered_flagged, function_rows,
    };
    use borer_engine::analysis::{Analysis, EnumSource, Overlay};
    use borer_engine::program::{Arch, Program, Section};
    use gpui::{AppContext as _, TestAppContext, VisualTestContext};
    use workspace::Workspace;

    use super::{Address, Grades, Work, grade_text, shown_for};
    use crate::app_view::AppWindow;
    use crate::app_view::tests::{
        CALLER, init, load_sample, open, open_caller, open_place, sample, shown,
    };
    use crate::binary::{Binary, Loading, StatusLine, kind};
    use crate::check_marks::tests::wrong_at;
    use crate::decompile_item::{DecompileItem, TabMode};
    use crate::places::Place;
    use crate::worker::{
        GradeCounts, LoadedBinary, check_blocking, grade_counts_blocking, run_engine,
    };

    /// Returns a raw x86-64 image of `code` in `.text` at 0x1000, entered there, analyzed
    /// under the app's names, as a loaded binary.
    ///
    /// # Panics
    ///
    /// Panics if the code is longer than an address can count.
    fn loaded_from(code: Vec<u8>) -> Arc<LoadedBinary> {
        let len = u64::try_from(code.len()).unwrap();
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let analysis = Analysis::compute(&program);
        let overlay = Overlay {
            enum_source: EnumSource::Binary,
            ..Overlay::default()
        };
        let rows = function_rows(
            &analysis,
            &overlay,
            None,
            FunctionOrder::Address,
            0,
            usize::MAX,
        );
        Arc::new(LoadedBinary {
            path: PathBuf::from("other.bin"),
            program: Arc::new(program),
            analysis: Arc::new(analysis),
            fingerprint: overlay.fingerprint(),
            overlay: Arc::new(overlay),
            initial_rows: Arc::new(rows),
            notes: Vec::new(),
            identity: String::new(),
        })
    }

    /// Returns a binary whose function at 0x1000 compares its argument with a constant.
    fn compare() -> Arc<LoadedBinary> {
        let mut code = vec![
            0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
            0x0f, 0x94, 0xc0, // ASM: sete al
            0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
            0xc3, // ASM: ret
        ];
        code.resize(0x10, 0xcc);
        loaded_from(code)
    }

    /// Returns a binary whose function at 0x1000 divides its argument by a constant, which
    /// the repair search can render another way.
    fn quotient() -> Arc<LoadedBinary> {
        let mut code = vec![
            0x89, 0xc8, // ASM: mov eax, ecx
            0xb9, 0xfb, 0xff, 0xff, 0xff, // ASM: mov ecx, 0xfffffffb
            0x99, // ASM: cdq
            0xf7, 0xf9, // ASM: idiv ecx
            0xc3, // ASM: ret
        ];
        code.resize(0x10, 0xcc);
        loaded_from(code)
    }

    /// Fills `loaded`'s memo as if the check had flagged 0x1000 under its names.
    ///
    /// The repair search is to have kept a rendering that masks the return. A flag is a
    /// check with a statement the machine does not bear out, so one disagreeing address
    /// makes it.
    fn flag(loaded: &LoadedBinary) {
        let block = BlockCheck::new(
            0x1000,
            Ok(Some("a state tried disagrees")),
            (1, 1),
            Vec::new(),
        );
        let check = TextCheck {
            blocks: vec![block],
            disagree: vec![0x1000],
        };
        let names = loaded.overlay.fingerprint();
        let derived = &loaded.analysis.derived;
        derived.get_or_build_item("text_check", names, 0x1000_u64, || Some(check), |_| 0);
        let kept = Repair::Repaired {
            moved: vec![Site::Return],
            tried: Vec::new(),
            checks: 1,
        };
        derived.get_or_build_item(
            "repair",
            names,
            (0x1000_u64, Budget::ANSWER),
            || kept,
            |_| 0,
        );
    }

    /// Returns the engine's check of the answer `loaded`'s function at `entry` is drawn with.
    ///
    /// # Panics
    ///
    /// Panics if the function has no checked answer.
    fn answer_check(loaded: &LoadedBinary, entry: u64) -> TextCheck {
        let (p, a) = (&loaded.program, &loaded.analysis);
        let (names, _) = answered_flagged(p, a, &loaded.overlay, entry);
        (*text_check(p, a, &names, entry)).clone().unwrap()
    }

    /// Returns the status item of type `T` in `workspace`'s status bar.
    ///
    /// # Panics
    ///
    /// Panics if the bar has none.
    fn item<T: workspace::StatusItemView>(
        workspace: &gpui::Entity<Workspace>,
        cx: &mut VisualTestContext,
    ) -> gpui::Entity<T> {
        workspace.read_with(cx, |workspace, cx| {
            workspace.status_bar().read(cx).item_of_type::<T>().unwrap()
        })
    }

    /// With nothing loaded the bar says so and shows no facts, grades or address; a load
    /// leads it with the engine's architecture and format, and an
    /// open function shows its address and the engine's grade counts of its blocks, the same
    /// counts the engine's check gives.
    ///
    /// # Panics
    ///
    /// Panics if an item shows something the binary or the engine does not hold.
    #[gpui::test]
    fn the_status_bar_shows_the_engines_facts(cx: &mut TestAppContext) {
        the_status_bar_shows_the_engines_facts_steps(cx);
    }

    /// Runs the steps of [`the_status_bar_shows_the_engines_facts`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_status_bar_shows_the_engines_facts`] says.
    fn the_status_bar_shows_the_engines_facts_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        cx.run_until_parked();
        let line = item::<StatusLine>(&app.workspace, cx);
        let grades = item::<Grades>(&app.workspace, cx);
        let address = item::<Address>(&app.workspace, cx);
        assert_eq!(
            line.read_with(cx, |line, cx| line.text(cx)),
            "No binary loaded"
        );
        assert!(
            app.binary
                .read_with(cx, |binary, _| binary.facts().is_empty())
        );
        assert!(grades.read_with(cx, |grades, _| grades.shown()).is_none());
        assert!(
            address
                .read_with(cx, |address, cx| address.shown(cx))
                .is_none()
        );
        load_sample(&app, cx);
        open_caller(&app.workspace, TabMode::Permanent, cx);
        assert_eq!(
            shown(&app.workspace, cx).map(|(entry, _)| entry),
            Some(CALLER)
        );
        let loaded = sample();
        let facts = app
            .binary
            .read_with(cx, |binary, _| binary.facts().to_vec());
        let leading = facts.first().map(|(text, _)| text.to_string());
        assert_eq!(leading, Some(kind(&loaded)));
        assert_eq!(address.read_with(cx, |a, cx| a.shown(cx)), Some(CALLER));
        let want = run_engine(|| grade_counts_blocking(&loaded, CALLER));
        assert!(want.is_some(), "the sample's caller is checked");
        let got = grades.read_with(cx, |grades, _| grades.shown());
        assert_eq!(got, want.map(|counts| (CALLER, counts)));
    }

    /// A cancelled load leaves the work item, drops its answer when it comes and says it
    /// was cancelled.
    ///
    /// # Panics
    ///
    /// Panics if the load still shows, or its answer lands.
    #[gpui::test]
    fn a_cancelled_load_is_dropped(cx: &mut TestAppContext) {
        a_cancelled_load_is_dropped_steps(cx);
    }

    /// Runs the steps of [`a_cancelled_load_is_dropped`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_cancelled_load_is_dropped`] says.
    fn a_cancelled_load_is_dropped_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let _work = item::<Work>(&app.workspace, cx);
        let missing = std::env::temp_dir().join("borer-app-missing-binary.exe");
        app.binary
            .update(cx, |binary, cx| binary.open_path(missing.clone(), cx));
        assert!(
            app.binary
                .read_with(cx, |binary, _| binary.reading().is_some())
        );
        app.binary.update(cx, |binary, cx| binary.cancel_load(cx));
        cx.run_until_parked();
        app.binary.read_with(cx, |binary, _| {
            assert!(binary.reading().is_none());
            assert!(binary.loaded().is_none());
            assert!(binary.load_error().is_none());
            assert_eq!(
                binary.status(),
                "cancelled reading borer-app-missing-binary.exe"
            );
        });
    }

    /// Grades are kept per loaded binary: a tab of another binary at the same address shows
    /// nothing until that binary's own check lands, then that check's counts.
    ///
    /// # Panics
    ///
    /// Panics if the bar shows one binary's counts for another.
    #[gpui::test]
    fn grades_follow_the_binary_not_only_the_address(cx: &mut TestAppContext) {
        grades_follow_the_binary_not_only_the_address_steps(cx);
    }

    /// Runs the steps of [`grades_follow_the_binary_not_only_the_address`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`grades_follow_the_binary_not_only_the_address`]
    /// says.
    fn grades_follow_the_binary_not_only_the_address_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        open_caller(&app.workspace, TabMode::Permanent, cx);
        assert_eq!(
            shown(&app.workspace, cx).map(|(entry, _)| entry),
            Some(CALLER)
        );
        let grades = item::<Grades>(&app.workspace, cx);
        assert!(grades.read_with(cx, |grades, _| grades.shown()).is_some());
        let other = compare();
        let want = run_engine(|| grade_counts_blocking(&other, CALLER));
        let place = Place::decompile(CALLER);
        open_place(&app.workspace, &other, place, TabMode::Permanent, cx);
        assert_eq!(grades.read_with(cx, |grades, _| grades.shown()), None);
        cx.run_until_parked();
        let got = grades.read_with(cx, |grades, _| grades.shown());
        assert_eq!(got, want.map(|counts| (CALLER, counts)));
    }

    /// Opens the sample's function at `entry` in a focused tab of `app`'s workspace.
    fn open_sample_at(app: &AppWindow, entry: u64, cx: &mut VisualTestContext) {
        let place = Place::decompile(entry);
        open_place(&app.workspace, &sample(), place, TabMode::Permanent, cx);
    }

    /// Redraws the active code tab of `app`'s workspace twice, as scrolling it does.
    ///
    /// # Panics
    ///
    /// Panics if no code tab is active.
    fn redraw_active_tab(app: &AppWindow, cx: &mut VisualTestContext) {
        let tab = app
            .workspace
            .read_with(cx, |workspace, cx| {
                workspace.active_item_as::<DecompileItem>(cx)
            })
            .unwrap();
        tab.update(cx, |_, cx| cx.notify());
        tab.update(cx, |_, cx| cx.notify());
    }

    /// A tab that changes while its check runs starts no second check.
    ///
    /// # Panics
    ///
    /// Panics if a redraw of the tab restarts the check.
    #[gpui::test]
    fn a_running_check_is_not_restarted(cx: &mut TestAppContext) {
        a_running_check_is_not_restarted_steps(cx);
    }

    /// Runs the steps of [`a_running_check_is_not_restarted`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_running_check_is_not_restarted`] says.
    fn a_running_check_is_not_restarted_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let grades = item::<Grades>(&app.workspace, cx);
        open_sample_at(&app, CALLER, cx);
        let started = grades.read_with(cx, |grades, _| grades.ticket());
        redraw_active_tab(&app, cx);
        assert_eq!(grades.read_with(cx, |grades, _| grades.ticket()), started);
    }

    /// A function the check flags and the repair search renders another way is graded as
    /// its answer is drawn, under the search's names, not as the flagged text.
    ///
    /// # Panics
    ///
    /// Panics if the counts are those of the flagged text.
    #[test]
    fn grades_are_those_of_the_answer_drawn() {
        let loaded = quotient();
        flag(&loaded);
        let got = run_engine(|| grade_counts_blocking(&loaded, 0x1000)).unwrap();
        let drawn = answer_check(&loaded, 0x1000);
        assert_eq!(got, GradeCounts::of(&drawn));
        assert_eq!(got.disagree, 0);
    }

    /// The bar's words and numbers are those of the answer's header line.
    ///
    /// # Panics
    ///
    /// Panics if a count the bar shows is not in the header as the bar words it.
    #[test]
    fn the_bar_counts_as_the_header_does() {
        let loaded = sample();
        let check = answer_check(&loaded, CALLER);
        let header = check.header();
        let counts = run_engine(|| grade_counts_blocking(&loaded, CALLER)).unwrap();
        assert_eq!(counts, GradeCounts::of(&check));
        assert!(
            header.contains(&grade_text(&counts, Grade::Proved)),
            "{header}"
        );
        for grade in [Grade::Tested, Grade::Unchecked] {
            if counts.count(grade) > 0 {
                assert!(header.contains(&grade_text(&counts, grade)), "{header}");
            }
        }
        assert_eq!(
            header.contains("disagree at"),
            counts.disagree > 0,
            "{header}"
        );
    }

    /// The work item stays hidden for the first tenth of a second of a load, then shows how
    /// long it has run, redrawn at that tenth and then a second after each redraw.
    ///
    /// # Panics
    ///
    /// Panics if it shows early, or redraws early or not at all.
    #[gpui::test]
    fn the_work_item_shows_after_a_tenth_of_a_second(cx: &mut TestAppContext) {
        the_work_item_shows_after_a_tenth_of_a_second_steps(cx);
    }

    /// Runs the steps of [`the_work_item_shows_after_a_tenth_of_a_second`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_work_item_shows_after_a_tenth_of_a_second`] says.
    fn the_work_item_shows_after_a_tenth_of_a_second_steps(cx: &mut TestAppContext) {
        let since = cx.executor().now();
        let loading = Loading {
            path: PathBuf::from("big.dll"),
            since,
        };
        assert_eq!(shown_for(&loading, since + Duration::from_millis(99)), None);
        let later = since + Duration::from_millis(1500);
        assert_eq!(
            shown_for(&loading, later),
            Some(Duration::from_millis(1500))
        );
        init(cx);
        let binary = cx.new(|cx| Binary::new(cx));
        let work = cx.new(|cx| Work::new(binary.clone(), cx));
        let redraws = Rc::new(Cell::new(0_u32));
        let count = redraws.clone();
        let _watch = cx.update(|cx| cx.observe(&work, move |_, _| count.set(count.get() + 1)));
        binary.update(cx, |binary, cx| {
            binary.show_reading(loading.path, since, cx);
        });
        cx.run_until_parked();
        let start = redraws.get();
        let step = |ms, cx: &mut TestAppContext| {
            cx.executor().advance_clock(Duration::from_millis(ms));
            redraws.get()
        };
        assert_eq!(step(99, cx), start, "redrawn before a tenth of a second");
        assert_eq!(step(1, cx), start + 1, "not redrawn at a tenth of a second");
        assert_eq!(
            step(999, cx),
            start + 1,
            "redrawn within a second of the last"
        );
        assert_eq!(
            step(1, cx),
            start + 2,
            "not redrawn a second after the last"
        );
    }

    /// A function the engine has no check of is not checked again on every redraw of its
    /// tab.
    ///
    /// # Panics
    ///
    /// Panics if a redraw starts another check.
    #[gpui::test]
    fn a_check_with_no_answer_is_not_repeated(cx: &mut TestAppContext) {
        a_check_with_no_answer_is_not_repeated_steps(cx);
    }

    /// Runs the steps of [`a_check_with_no_answer_is_not_repeated`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_check_with_no_answer_is_not_repeated`] says.
    fn a_check_with_no_answer_is_not_repeated_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let grades = item::<Grades>(&app.workspace, cx);
        let nowhere = 0x5;
        open_sample_at(&app, nowhere, cx);
        cx.run_until_parked();
        assert_eq!(grades.read_with(cx, |grades, _| grades.shown()), None);
        let settled = grades.read_with(cx, |grades, _| grades.ticket());
        redraw_active_tab(&app, cx);
        cx.run_until_parked();
        assert_eq!(grades.read_with(cx, |grades, _| grades.ticket()), settled);
    }

    /// A recheck that finds a block wrong shows in the bar: one block fewer proved and one
    /// instruction that disagrees.
    ///
    /// # Panics
    ///
    /// Panics if the bar does not count the recheck.
    #[gpui::test]
    fn a_recheck_shows_in_the_bar(cx: &mut TestAppContext) {
        a_recheck_shows_in_the_bar_steps(cx);
    }

    /// Runs the steps of [`a_recheck_shows_in_the_bar`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_recheck_shows_in_the_bar`] says.
    fn a_recheck_shows_in_the_bar_steps(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let grades = item::<Grades>(&app.workspace, cx);
        let loaded = sample();
        open_place(
            &app.workspace,
            &loaded,
            Place::decompile(CALLER),
            TabMode::Permanent,
            cx,
        );
        cx.run_until_parked();
        let before = grades.read_with(cx, |g, _| g.shown()).unwrap().1;
        assert_eq!(before.disagree, 0);
        let check = run_engine(|| check_blocking(&loaded, CALLER));
        let at = (loaded.state(), CALLER);
        let record = wrong_at(CALLER);
        app.binary
            .update(cx, |b, cx| b.put_recheck(at, &check, record, cx));
        cx.run_until_parked();
        let after = grades.read_with(cx, |g, _| g.shown()).unwrap().1;
        assert_eq!(after.disagree, 1);
        assert_eq!(after.proved, before.proved - 1);
    }
}
