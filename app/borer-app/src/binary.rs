//! The binary a window has open: its background load, its load status, the binaries opened
//! before it, and the status-bar item that shows that status.

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use gpui::{
    App, Context, Entity, EventEmitter, Global, IntoElement, ParentElement as _, PathPromptOptions,
    Render, SharedString, Styled as _, Subscription, Task, Window,
};
use ui::{Color, Label, LabelCommon as _, LabelSize, h_flex};
use workspace::{HideStatusItem, ItemHandle, StatusItemView};

use crate::recent::{self, RecentBinary, file_name};
use borer_engine::cancel::Cancel;

use crate::worker::{LoadedBinary, load_binary_blocking, spawn_engine};

/// Returns what a load of `path` is called while it runs: `Reading` and the file's name.
///
/// # Arguments
///
/// * `path` - The file the load reads.
#[must_use]
pub fn reading_label(path: &Path) -> SharedString {
    format!("Reading {}", file_name(path)).into()
}

/// Note appended to load status lines saying what this direct engine load omits.
pub const LOAD_SCOPE_NOTE: &str = "packs left out; session load path comes next";

/// The status line while no binary is open.
pub const NO_BINARY: &str = "No binary loaded";

/// How the status line starts while an open waits for a running load's engine thread.
pub const STILL_READING: &str = "still reading";

/// A load that is running: what it reads and since when.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Loading {
    /// The binary being read.
    pub path: PathBuf,
    /// When the load started, on the executor's clock.
    pub since: Instant,
}

impl Loading {
    /// Returns the file name of the binary being read, the whole path when it has none.
    #[must_use]
    pub fn name(&self) -> String {
        file_name(&self.path)
    }
}

/// What changed in a window's binary.
#[derive(Debug, Clone)]
pub enum BinaryEvent {
    /// A load finished or a binary was shown: the functions panel lists this binary.
    Opened(Arc<LoadedBinary>),
    /// No binary is open any more: a load started, failed or was cancelled, or the binary
    /// was closed.
    Closed,
}

/// The binary a window has open, or is loading, and the status line of that load.
pub struct Binary {
    /// The analyzed binary, once a load has finished.
    loaded: Option<Arc<LoadedBinary>>,
    /// What the status line leads with for [`Self::loaded`], built when it loaded.
    facts: Vec<(SharedString, Color)>,
    /// Error text of the most recent failed load.
    error: Option<String>,
    /// The running load, `None` once it finished or before any.
    reading: Option<Loading>,
    /// The file whose engine load is still running, shown or cancelled: the engine's
    /// analysis checks no cancel flag yet, so a cancelled load keeps its thread until it ends.
    busy: Option<PathBuf>,
    /// Status line the status bar shows.
    status: String,
    /// The binaries opened before, the newest first.
    recent: Vec<RecentBinary>,
    /// Flag of the running load; raising it drops the load's answer.
    load_flag: Cancel,
    /// The running background load.
    load_task: Option<Task<()>>,
    /// The running file dialog.
    prompt_task: Option<Task<()>>,
    /// The running write of the binaries opened before.
    remember_task: Option<Task<()>>,
}

impl EventEmitter<BinaryEvent> for Binary {}

impl std::fmt::Debug for Binary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Binary")
            .field("status", &self.status)
            .finish_non_exhaustive()
    }
}

impl Binary {
    /// Returns a window's binary with none open, and the binaries opened before as the
    /// key-value store keeps them; a store that cannot be read says so on the status line.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the store.
    #[must_use]
    pub fn new(cx: &App) -> Self {
        let (recent, status) = match recent::read(cx) {
            Ok(recent) => (recent, NO_BINARY.to_owned()),
            Err(err) => (Vec::new(), format!("recent binaries not read: {err:#}")),
        };
        Self {
            loaded: None,
            facts: Vec::new(),
            error: None,
            reading: None,
            busy: None,
            status,
            recent,
            load_flag: Cancel::new(),
            load_task: None,
            prompt_task: None,
            remember_task: None,
        }
    }

    /// Returns the facts the status line leads with, each with the color it draws in: the
    /// binary's architecture and format, soft, then the engine's count of its functions,
    /// muted; built once per load, none before one finished.
    #[must_use]
    pub fn facts(&self) -> &[(SharedString, Color)] {
        &self.facts
    }

    /// Returns the analyzed binary, once a load has finished.
    #[must_use]
    pub const fn loaded(&self) -> Option<&Arc<LoadedBinary>> {
        self.loaded.as_ref()
    }

    /// Returns the error of the most recent failed load, if any.
    #[must_use]
    pub fn load_error(&self) -> Option<&str> {
        self.error.as_deref()
    }

    /// Returns the running load, `None` when no load runs.
    #[must_use]
    pub const fn reading(&self) -> Option<&Loading> {
        self.reading.as_ref()
    }

    /// Returns the file whose engine load still runs, shown or cancelled, if any; no other
    /// load starts until it ends.
    #[must_use]
    pub fn busy(&self) -> Option<&Path> {
        self.busy.as_deref()
    }

    /// Returns the binaries opened before, the newest first.
    #[must_use]
    pub fn recent(&self) -> &[RecentBinary] {
        &self.recent
    }

    /// Returns the status line of the load.
    #[must_use]
    pub fn status(&self) -> &str {
        &self.status
    }

    /// Replaces the status line with `status`.
    ///
    /// # Arguments
    ///
    /// * `status` - The new status line.
    /// * `cx` - Binary context.
    pub fn set_status(&mut self, status: String, cx: &mut Context<'_, Self>) {
        self.status = status;
        cx.notify();
    }

    /// Opens the system file dialog and loads the chosen binary in the background.
    ///
    /// # Arguments
    ///
    /// * `cx` - Binary context spawning the dialog receiver task.
    pub fn prompt_open(&mut self, cx: &mut Context<'_, Self>) {
        let receiver = cx.prompt_for_paths(PathPromptOptions {
            files: true,
            directories: false,
            multiple: false,
            prompt: None,
        });
        self.prompt_task = Some(cx.spawn(async move |this, cx| {
            let Ok(outcome) = receiver.await else {
                return;
            };
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |binary, cx| match outcome {
                Ok(Some(mut paths)) => {
                    if let Some(path) = paths.pop() {
                        binary.open_path(path, cx);
                    }
                }
                Ok(None) => {}
                Err(err) => binary.set_status(format!("open dialog failed: {err:#}"), cx),
            });
        }));
    }

    /// Starts loading and analyzing `path` on the background executor, dropping the
    /// binary open before it, unless an engine load still runs.
    ///
    /// A load the person cancelled keeps the engine busy until its analysis ends, so a
    /// second load is refused until then rather than run beside it, and the status line
    /// says so.
    ///
    /// # Arguments
    ///
    /// * `path` - File path of the binary to load.
    /// * `cx` - Binary context spawning the background task.
    ///
    /// # Returns
    ///
    /// Whether the load started.
    pub fn open_path(&mut self, path: PathBuf, cx: &mut Context<'_, Self>) -> bool {
        if let Some(busy) = &self.busy {
            self.status = format!(
                "{STILL_READING} {}; open it again once that ends",
                file_name(busy)
            );
            cx.notify();
            return false;
        }
        self.busy = Some(path.clone());
        self.loaded = None;
        self.facts.clear();
        self.error = None;
        self.status.clear();
        self.reading = Some(Loading {
            path: path.clone(),
            since: cx.background_executor().now(),
        });
        cx.emit(BinaryEvent::Closed);
        cx.notify();
        let request = spawn_engine(reading_label(&path), cx, move || load_binary_blocking(path));
        self.load_flag = request.flag();
        self.load_task = Some(cx.spawn(async move |this, cx| {
            let result = request.await;
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |binary, cx| {
                binary.busy = None;
                if let Some(result) = result.filter(|_| binary.reading.is_some()) {
                    binary.finish_load(result, cx);
                } else {
                    if binary.status.starts_with(STILL_READING) {
                        binary.status = NO_BINARY.to_owned();
                    }
                    cx.notify();
                }
            });
        }));
        true
    }

    /// Closes the open binary, or stops its load, and shows that none is open.
    ///
    /// # Arguments
    ///
    /// * `cx` - Binary context.
    pub fn close(&mut self, cx: &mut Context<'_, Self>) {
        self.load_flag.raise();
        self.reading = None;
        self.facts.clear();
        self.loaded = None;
        self.error = None;
        self.status = NO_BINARY.to_owned();
        cx.emit(BinaryEvent::Closed);
        cx.notify();
    }

    /// Stops showing the running load and drops its answer when it comes.
    ///
    /// The engine's analysis checks no cancel flag yet, so its thread runs to the end of the
    /// analysis and [`Self::busy`] holds until then.
    ///
    /// # Arguments
    ///
    /// * `cx` - Binary context.
    pub fn cancel_load(&mut self, cx: &mut Context<'_, Self>) {
        let Some(loading) = self.reading.take() else {
            return;
        };
        self.load_flag.raise();
        self.status = format!("cancelled reading {}", loading.name());
        cx.emit(BinaryEvent::Closed);
        cx.notify();
    }

    /// Applies the result of a background load.
    ///
    /// # Arguments
    ///
    /// * `result` - Outcome of [`load_binary_blocking`].
    /// * `cx` - Binary context.
    pub(crate) fn finish_load(
        &mut self,
        result: anyhow::Result<Arc<LoadedBinary>>,
        cx: &mut Context<'_, Self>,
    ) {
        self.reading = None;
        match result {
            Ok(loaded) => self.show_loaded(loaded, cx),
            Err(err) => {
                let msg = format!("{err:#}");
                self.status = format!("load failed: {msg}");
                self.error = Some(msg);
                cx.emit(BinaryEvent::Closed);
                cx.notify();
            }
        }
    }

    /// Shows `loaded` as the open binary and puts it first among the binaries opened
    /// before, writing that list back in the background.
    ///
    /// # Arguments
    ///
    /// * `loaded` - A binary the engine loaded and analyzed.
    /// * `cx` - Binary context.
    pub fn show_loaded(&mut self, loaded: Arc<LoadedBinary>, cx: &mut Context<'_, Self>) {
        self.status = format!("{} ({LOAD_SCOPE_NOTE})", loaded.path.display());
        let kind = kind(&loaded);
        let count = loaded.initial_rows.counts();
        self.facts = vec![
            (kind.clone().into(), Color::Muted),
            (count.into(), Color::Placeholder),
        ];
        let opened = RecentBinary {
            path: std::path::absolute(&loaded.path).unwrap_or_else(|_| loaded.path.clone()),
            kind,
        };
        self.recent = recent::remembered(std::mem::take(&mut self.recent), opened);
        let write = recent::write(&self.recent, cx);
        self.remember_task = Some(cx.spawn(async move |this, cx| {
            let Err(err) = write.await else {
                return;
            };
            let Some(this) = this.upgrade() else {
                return;
            };
            let why = format!("recent binaries not kept: {err:#}");
            this.update(cx, |binary, cx| binary.set_status(why, cx));
        }));
        self.loaded = Some(loaded.clone());
        cx.emit(BinaryEvent::Opened(loaded));
        cx.notify();
    }
}

/// Returns the engine's architecture and format of `loaded`, as `x86-64 PE`.
///
/// # Arguments
///
/// * `loaded` - A loaded binary.
#[must_use]
pub fn kind(loaded: &LoadedBinary) -> String {
    let program = &loaded.program;
    format!("{} {}", program.arch.name(), program.format.name())
}

/// The status-bar item showing a [`Binary`]'s status line.
pub struct StatusLine {
    /// The binary whose status this shows.
    binary: Entity<Binary>,
    /// Repaints the line when the binary or the settings notice changes.
    _observe: [Subscription; 2],
}

/// What went wrong with the person's settings file, read at startup or written by a theme
/// action, `None` while nothing did; every status line shows it before the binary's status.
#[derive(Debug, Clone, Default)]
pub struct SettingsNotice(pub Option<SharedString>);

impl Global for SettingsNotice {}

impl std::fmt::Debug for StatusLine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StatusLine").finish_non_exhaustive()
    }
}

impl StatusLine {
    /// Returns the status-bar item for `binary`.
    ///
    /// # Arguments
    ///
    /// * `binary` - The binary whose status line to show.
    /// * `cx` - Status line context.
    #[must_use]
    pub fn new(binary: Entity<Binary>, cx: &mut Context<'_, Self>) -> Self {
        let observe = [
            cx.observe(&binary, |_, _, cx| cx.notify()),
            cx.observe_global::<SettingsNotice>(|_, cx| cx.notify()),
        ];
        Self {
            binary,
            _observe: observe,
        }
    }

    /// Returns the binary whose status this shows.
    #[must_use]
    pub const fn binary(&self) -> &Entity<Binary> {
        &self.binary
    }

    /// Returns the line's text: the settings notice, if any, then the binary's status.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the binary and the notice.
    #[must_use]
    pub fn text(&self, cx: &App) -> String {
        let status = self.binary.read(cx).status();
        match cx.try_global::<SettingsNotice>().and_then(|n| n.0.as_ref()) {
            Some(notice) if status.is_empty() => notice.to_string(),
            Some(notice) => format!("{notice}; {status}"),
            None => status.to_owned(),
        }
    }
}

/// Returns a status-bar label saying `text` in `color`.
///
/// # Arguments
///
/// * `text` - What it says.
/// * `color` - Its color.
pub(crate) fn status_label(text: impl Into<SharedString>, color: Color) -> Label {
    Label::new(text).size(LabelSize::Small).color(color)
}

impl Render for StatusLine {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let facts = self.binary.read(cx).facts().iter();
        h_flex()
            .gap_3()
            .children(facts.map(|(text, color)| status_label(text.clone(), *color)))
            .child(status_label(self.text(cx), Color::Placeholder))
    }
}

impl StatusItemView for StatusLine {
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

#[cfg(test)]
impl Binary {
    /// Shows `path` as read since `since` with no engine load behind it, for tests of what
    /// draws a running load over time.
    ///
    /// # Arguments
    ///
    /// * `path` - The file shown as read.
    /// * `since` - When the shown load started, on the executor's clock.
    /// * `cx` - Binary context.
    pub(crate) fn show_reading(
        &mut self,
        path: PathBuf,
        since: Instant,
        cx: &mut Context<'_, Self>,
    ) {
        self.reading = Some(Loading { path, since });
        cx.notify();
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::render::{FunctionRows, LeftOut};
    use gpui::{AppContext as _, SharedString, TestAppContext};
    use ui::Color;

    use super::{Binary, STILL_READING};
    use crate::app_view::tests::sample;
    use crate::worker::LoadedBinary;

    /// The status line leads with the engine's architecture and format of the open binary,
    /// soft, then the engine's count of its functions with what it left out, muted; nothing
    /// before a load, and nothing again once another load starts.
    ///
    /// # Panics
    ///
    /// Panics if the facts say anything else.
    #[gpui::test]
    fn the_status_line_leads_with_the_binarys_facts(cx: &mut TestAppContext) {
        the_status_line_leads_with_the_binarys_facts_steps(cx);
    }

    /// Runs the steps of [`the_status_line_leads_with_the_binarys_facts`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`the_status_line_leads_with_the_binarys_facts`]
    /// says.
    fn the_status_line_leads_with_the_binarys_facts_steps(cx: &mut TestAppContext) {
        let binary = cx.new(|cx| Binary::new(cx));
        let facts =
            |cx: &mut TestAppContext| binary.read_with(cx, |binary, _| binary.facts().to_vec());
        assert!(facts(cx).is_empty());
        let sample = sample();
        let rows = FunctionRows {
            left_out: LeftOut {
                thunks: 2,
                funclets: 1,
            },
            ..(*sample.initial_rows).clone()
        };
        let loaded = Arc::new(LoadedBinary {
            path: sample.path.clone(),
            program: sample.program.clone(),
            analysis: sample.analysis.clone(),
            overlay: sample.overlay.clone(),
            initial_rows: Arc::new(rows),
        });
        binary.update(cx, |binary, cx| binary.finish_load(Ok(loaded.clone()), cx));
        let program = &loaded.program;
        let kind = format!("{} {}", program.arch.name(), program.format.name());
        let count = format!(
            "{} functions; 2 import thunks left out, filter=thunk lists them; \
             1 exception funclets left out, filter=funclet lists them",
            loaded.initial_rows.total
        );
        let want = vec![
            (SharedString::from(kind), Color::Muted),
            (SharedString::from(count), Color::Placeholder),
        ];
        assert_eq!(facts(cx), want);
        let missing = std::env::temp_dir().join("borer-app-no-such-binary.exe");
        binary.update(cx, |binary, cx| binary.open_path(missing, cx));
        assert!(facts(cx).is_empty());
    }

    /// A second open is refused while a load reads its file, and again after that load is
    /// cancelled until its engine thread ends; then it starts.
    ///
    /// # Panics
    ///
    /// Panics if a second load starts beside a running one.
    #[gpui::test]
    fn a_second_load_waits_for_the_engine(cx: &mut TestAppContext) {
        a_second_load_waits_for_the_engine_steps(cx);
    }

    /// Runs the steps of [`a_second_load_waits_for_the_engine`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_second_load_waits_for_the_engine`] says.
    fn a_second_load_waits_for_the_engine_steps(cx: &mut TestAppContext) {
        crate::app_view::tests::init(cx);
        let binary = cx.new(|cx| Binary::new(cx));
        let first = std::env::temp_dir().join("borer-app-first-missing.exe");
        let second = std::env::temp_dir().join("borer-app-second-missing.exe");
        let open = |path: &std::path::PathBuf, cx: &mut TestAppContext| {
            binary.update(cx, |binary, cx| binary.open_path(path.clone(), cx))
        };
        assert!(open(&first, cx));
        assert!(!open(&second, cx));
        binary.update(cx, |binary, cx| binary.cancel_load(cx));
        assert!(binary.read_with(cx, |binary, _| binary.reading().is_none()));
        assert!(!open(&second, cx));
        cx.run_until_parked();
        assert!(binary.read_with(cx, |binary, _| binary.busy().is_none()));
        assert!(open(&second, cx));
    }

    /// A refused open's line goes once the cancelled load it waited for ends.
    ///
    /// # Panics
    ///
    /// Panics if the line stays after the engine thread ended.
    #[gpui::test]
    fn a_refused_open_line_goes_when_the_load_ends(cx: &mut TestAppContext) {
        a_refused_open_line_goes_when_the_load_ends_steps(cx);
    }

    /// Runs the steps of [`a_refused_open_line_goes_when_the_load_ends`].
    ///
    /// # Panics
    ///
    /// Panics when a step goes wrong, as [`a_refused_open_line_goes_when_the_load_ends`] says.
    fn a_refused_open_line_goes_when_the_load_ends_steps(cx: &mut TestAppContext) {
        crate::app_view::tests::init(cx);
        let binary = cx.new(|cx| Binary::new(cx));
        let a = std::env::temp_dir().join("borer-app-a-missing.exe");
        let b = std::env::temp_dir().join("borer-app-b-missing.exe");
        assert!(binary.update(cx, |binary, cx| binary.open_path(a, cx)));
        binary.update(cx, |binary, cx| binary.cancel_load(cx));
        assert!(!binary.update(cx, |binary, cx| binary.open_path(b, cx)));
        let status = |cx: &mut TestAppContext| binary.read_with(cx, |b, _| b.status().to_owned());
        assert!(status(cx).starts_with(STILL_READING));
        cx.run_until_parked();
        assert!(!status(cx).starts_with(STILL_READING), "{}", status(cx));
    }
}
