//! The binary a window has open: its background load, its edits and project file, its load
//! status, the binaries opened before it, and the status-bar item that shows that status.

use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use borer_engine::analysis::edit::Edit;
use borer_engine::analysis::project::{Foreign, Project};
use futures::channel::oneshot;
use gpui::{
    AnyWindowHandle, App, Context, Entity, EventEmitter, Global, IntoElement, ParentElement as _,
    PathPromptOptions, PromptLevel, Render, SharedString, Styled as _, Subscription, Task, Window,
};
use ui::{Color, Label, LabelCommon as _, LabelSize, h_flex};
use workspace::{HideStatusItem, ItemHandle, StatusItemView, Workspace};

use borer_engine::cancel::Cancel;

use crate::actions::{OpenProject, SaveProject, SaveProjectAs};
use crate::recent::{self, RecentBinary, file_name};
use crate::worker::{
    Job, LoadedBinary, edit_blocking, load_binary_blocking, open_project_blocking,
    read_project_blocking, save_project_blocking, spawn_engine,
};

/// Returns what a load of `path` is called while it runs: `Reading` and the file's name.
///
/// # Arguments
///
/// * `path` - The file the load reads.
#[must_use]
pub fn reading_label(path: &Path) -> SharedString {
    format!("Reading {}", file_name(path)).into()
}

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
    /// An edit or a project changed the names, comments or types of the open binary: views
    /// ask again over this state and keep their place.
    Revised(Arc<LoadedBinary>),
    /// No binary is open any more: a load started, failed or was cancelled, or the binary
    /// was closed.
    Closed,
}

/// A view over a state of the window's binary, which says which state it shows, so a check
/// can find a view an edit left behind.
pub trait Revision {
    /// Returns the [`LoadedBinary::fingerprint`] of the state the view shows, `None` while it
    /// shows none.
    fn revision(&self) -> Option<u64>;
}

/// What the window title ends the binary's name with while its overlay holds edits no
/// project file has.
pub const UNSAVED: &str = " *";

/// The binary a window has open, or is loading, and the status line of that load.
///
/// Its state is an immutable [`LoadedBinary`] that views read; an edit or a project open
/// makes the next one in the background and swaps it in here.
pub struct Binary {
    /// The analyzed binary, once a load has finished.
    loaded: Option<Arc<LoadedBinary>>,
    /// What the status line leads with for [`Self::loaded`], built when it loaded.
    facts: Vec<(SharedString, Color)>,
    /// The project file last saved or opened for the binary.
    project: Option<PathBuf>,
    /// [`LoadedBinary::fingerprint`] of the overlay last saved, opened or loaded.
    saved: u64,
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
    /// The running edit, project open or save, one at a time.
    edit: Job,
    /// What [`Self::edit`] runs, `None` while nothing does.
    editing: Option<String>,
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
            project: None,
            saved: 0,
            error: None,
            reading: None,
            busy: None,
            status,
            recent,
            load_flag: Cancel::new(),
            load_task: None,
            prompt_task: None,
            remember_task: None,
            edit: Job::default(),
            editing: None,
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

    /// Returns whether a binary is open: loaded, or being read, which Close Binary stops.
    #[must_use]
    pub const fn is_open(&self) -> bool {
        self.loaded.is_some() || self.reading.is_some()
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

    /// Returns whether the overlay holds edits that the project file last saved or opened
    /// does not.
    #[must_use]
    pub fn is_unsaved(&self) -> bool {
        self.loaded
            .as_ref()
            .is_some_and(|loaded| loaded.fingerprint != self.saved)
    }

    /// Returns what the window's title calls the open binary: its file name, [`UNSAVED`]
    /// while [`Self::is_unsaved`], and the project file's name; `borer` with none open.
    #[must_use]
    pub fn title(&self) -> String {
        let Some(loaded) = &self.loaded else {
            return "borer".to_owned();
        };
        let mark = if self.is_unsaved() { UNSAVED } else { "" };
        let project = self
            .project
            .as_deref()
            .map_or_else(String::new, |path| format!(" ({})", file_name(path)));
        format!("{}{mark}{project}", file_name(&loaded.path))
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

    /// Opens the system file dialog as `options` say and hands the paths the person picks to
    /// `then`; a cancelled dialog does nothing, and one that fails says so on the status line.
    ///
    /// # Arguments
    ///
    /// * `options` - What the dialog picks.
    /// * `then` - Takes the binary and the picked paths, at least one.
    /// * `cx` - Binary context spawning the dialog receiver task.
    pub fn pick(
        &mut self,
        options: PathPromptOptions,
        then: impl FnOnce(&mut Self, Vec<PathBuf>, &mut Context<'_, Self>) + 'static,
        cx: &mut Context<'_, Self>,
    ) {
        let answer = ask_paths(options, cx);
        self.on_dialog(
            answer,
            |binary, paths, cx| {
                if !paths.is_empty() {
                    then(binary, paths, cx);
                }
            },
            cx,
        );
    }

    /// Hands what a system file dialog answers to `then`; a cancelled dialog does nothing,
    /// and one that fails says so on the status line.
    ///
    /// # Arguments
    ///
    /// * `answer` - The dialog's answer, as gpui's dialogs give it.
    /// * `then` - Takes the binary and what the person picked.
    /// * `cx` - Binary context spawning the receiver task.
    fn on_dialog<T: 'static, E>(
        &mut self,
        answer: impl Future<Output = Result<anyhow::Result<Option<T>>, E>> + 'static,
        then: impl FnOnce(&mut Self, T, &mut Context<'_, Self>) + 'static,
        cx: &mut Context<'_, Self>,
    ) {
        self.prompt_task = Some(cx.spawn(async move |this, cx| {
            let Ok(outcome) = answer.await else {
                return;
            };
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |binary, cx| match outcome {
                Ok(Some(picked)) => then(binary, picked, cx),
                Ok(None) => {}
                Err(err) => binary.set_status(format!("file dialog failed: {err:#}"), cx),
            });
        }));
    }

    /// Opens the system file dialog and loads the chosen binary in the background.
    ///
    /// # Arguments
    ///
    /// * `cx` - Binary context spawning the dialog receiver task.
    pub fn prompt_open(&mut self, cx: &mut Context<'_, Self>) {
        self.pick(
            ONE_FILE,
            |binary, mut paths, cx| {
                if let Some(path) = paths.pop() {
                    binary.open_path(path, cx);
                }
            },
            cx,
        );
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
        self.project = None;
        self.error = None;
        self.status.clear();
        self.reading = Some(Loading {
            path: path.clone(),
            since: cx.background_executor().now(),
        });
        cx.emit(BinaryEvent::Closed);
        cx.notify();
        let (sources, notes) = crate::stored::sources(cx);
        let label = reading_label(&path);
        let work = move || load_binary_blocking(path, &sources, notes);
        let request = spawn_engine(label, cx, work);
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
        let notes: String = loaded
            .notes
            .iter()
            .map(|note| format!("; {note}"))
            .collect();
        self.status = format!("{}{notes}", loaded.path.display());
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
        self.saved = loaded.fingerprint;
        self.loaded = Some(loaded.clone());
        cx.emit(BinaryEvent::Opened(loaded));
        cx.notify();
    }

    /// Runs `work`, labelled `label`, over the open state in the edit job and hands `done`
    /// the state it ran over and what it returned; with no binary open, or while another
    /// edit, project open or save runs, says so on the status line instead.
    ///
    /// # Arguments
    ///
    /// * `label` - What the job list calls the work.
    /// * `work` - Engine work over the open state.
    /// * `done` - Takes the binary, the state `work` ran over, and its result.
    /// * `cx` - Binary context.
    fn run<R: Send + Unpin + 'static>(
        &mut self,
        label: String,
        work: impl FnOnce(&LoadedBinary) -> R + Send + 'static,
        done: impl FnOnce(&mut Self, Arc<LoadedBinary>, R, &mut Context<'_, Self>) + 'static,
        cx: &mut Context<'_, Self>,
    ) {
        let Some(base) = self.loaded.clone() else {
            self.set_status("open a binary first".to_owned(), cx);
            return;
        };
        if let Some(running) = &self.editing {
            let why = format!("{label} refused: {running} still runs; do it again once it ends");
            self.set_status(why, cx);
            return;
        }
        self.editing = Some(label.clone());
        let worked = base.clone();
        let work = move || work(&worked);
        self.edit.run(label, cx, work, move |binary, out, cx| {
            binary.editing = None;
            done(binary, base, out, cx);
        });
    }

    /// Puts `next`, made over `base`, in place of the open state, unless another edit, a
    /// project or a binary replaced `base` first, which the status line then says.
    ///
    /// # Arguments
    ///
    /// * `base` - The state `next` was made over.
    /// * `next` - The state to show.
    /// * `cx` - Binary context.
    ///
    /// # Returns
    ///
    /// Whether `next` is now the open state.
    fn advance(
        &mut self,
        base: &Arc<LoadedBinary>,
        next: Arc<LoadedBinary>,
        cx: &mut Context<'_, Self>,
    ) -> bool {
        if !self
            .loaded
            .as_ref()
            .is_some_and(|now| Arc::ptr_eq(now, base))
        {
            let why = "dropped: another edit, project or binary landed first; do it again";
            self.set_status(why.to_owned(), cx);
            return false;
        }
        self.loaded = Some(next.clone());
        cx.emit(BinaryEvent::Revised(next));
        cx.notify();
        true
    }

    /// Plans and commits `edits` through the engine's edit path in the background, the same
    /// path the server's annotating tools take, and shows the overlay they leave.
    ///
    /// # Arguments
    ///
    /// * `edits` - The edits, in order.
    /// * `cx` - Binary context.
    pub fn edit(&mut self, edits: Vec<Edit>, cx: &mut Context<'_, Self>) {
        let label = match edits.first() {
            Some(Edit::Name { at, .. }) => format!("Renaming {at:#x}"),
            _ => "Editing".to_owned(),
        };
        self.run(
            label,
            move |loaded| edit_blocking(loaded, &edits),
            |binary, base, out, cx| match out {
                Ok((next, changes)) => {
                    if binary.advance(&base, next, cx) {
                        binary.set_status(format!("{changes} overlay entries changed"), cx);
                    }
                }
                Err(err) => binary.set_status(format!("edit refused: {err:#}"), cx),
            },
            cx,
        );
    }

    /// Opens the system file dialog for a project file and opens the one picked.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the questions about it are asked in.
    /// * `cx` - Binary context.
    pub fn prompt_open_project(&mut self, window: AnyWindowHandle, cx: &mut Context<'_, Self>) {
        let options = PathPromptOptions {
            files: true,
            directories: false,
            multiple: false,
            prompt: None,
        };
        self.pick(
            options,
            move |binary, mut paths, cx| {
                if let Some(path) = paths.pop() {
                    binary.open_project(path, window, cx);
                }
            },
            cx,
        );
    }

    /// Opens the project file at `path` as the engine admits it, in the background, and
    /// says what it loaded and skipped as the engine words it.
    ///
    /// Over edits no project file holds it first asks in `window` whether to drop them. A
    /// refusal is the status line's, in the engine's words; one of a project saved for
    /// another binary also asks in `window` whether to force the file as it was read.
    ///
    /// # Arguments
    ///
    /// * `path` - The project file.
    /// * `window` - Window the questions are asked in.
    /// * `cx` - Binary context.
    pub fn open_project(
        &mut self,
        path: PathBuf,
        window: AnyWindowHandle,
        cx: &mut Context<'_, Self>,
    ) {
        if !self.is_unsaved() {
            self.read_project(path, window, cx);
            return;
        }
        let question = format!(
            "The binary has edits no project file holds; opening {} replaces them.",
            path.display()
        );
        Self::confirm(
            window,
            &question,
            "Open",
            move |binary, cx| binary.read_project(path, window, cx),
            cx,
        );
    }

    /// Reads the project file at `path` in the background and admits it unforced.
    ///
    /// # Arguments
    ///
    /// * `path` - The project file.
    /// * `window` - Window a refusal's force choice is asked in.
    /// * `cx` - Binary context.
    fn read_project(&mut self, path: PathBuf, window: AnyWindowHandle, cx: &mut Context<'_, Self>) {
        let file = path.clone();
        let label = format!("Reading project {}", file_name(&path));
        self.run(
            label,
            move |_| read_project_blocking(&file),
            move |binary, _, out, cx| match out {
                Ok(project) => binary.admit(path, Arc::new(project), false, window, cx),
                Err(err) => binary.set_status(format!("project not read: {err:#}"), cx),
            },
            cx,
        );
    }

    /// Puts the annotations of `file`, read from `path`, in place of the overlay as the
    /// engine admits them, in the background. A project forced over another build is not
    /// the open binary's own file, so the next save asks where to write.
    ///
    /// # Arguments
    ///
    /// * `path` - Where `file` was read from.
    /// * `file` - The project as read, which a force choice admits again unchanged.
    /// * `force` - Whether a project saved for another binary is admitted.
    /// * `window` - Window a refusal's force choice is asked in.
    /// * `cx` - Binary context.
    fn admit(
        &mut self,
        path: PathBuf,
        file: Arc<Project>,
        force: bool,
        window: AnyWindowHandle,
        cx: &mut Context<'_, Self>,
    ) {
        let kept = file.clone();
        let label = format!("Opening project {}", file_name(&path));
        self.run(
            label,
            move |loaded| open_project_blocking(loaded, &kept, force),
            move |binary, base, out, cx| match out {
                Ok((next, said)) => {
                    let saved = next.fingerprint;
                    if binary.advance(&base, next, cx) {
                        binary.saved = saved;
                        let said: Vec<&str> = said.lines().filter(|l| !l.is_empty()).collect();
                        let status = format!("project {}: {}", path.display(), said.join("; "));
                        binary.project = (!force).then_some(path);
                        binary.set_status(status, cx);
                    }
                }
                Err(err) => {
                    let why = format!("{err:#}");
                    binary.set_status(format!("project refused: {why}"), cx);
                    if err.downcast_ref::<Foreign>().is_some() {
                        Self::confirm(
                            window,
                            &why,
                            "Force",
                            move |binary, cx| binary.admit(path, file, true, window, cx),
                            cx,
                        );
                    }
                }
            },
            cx,
        );
    }

    /// Asks `question` in `window` with `yes` and Cancel, and runs `then` on the binary when
    /// the person picks `yes`.
    ///
    /// # Arguments
    ///
    /// * `window` - Window the question is asked in.
    /// * `question` - What is asked.
    /// * `yes` - The answer that runs `then`.
    /// * `then` - What that answer does.
    /// * `cx` - Binary context.
    fn confirm(
        window: AnyWindowHandle,
        question: &str,
        yes: &'static str,
        then: impl FnOnce(&mut Self, &mut Context<'_, Self>) + 'static,
        cx: &mut Context<'_, Self>,
    ) {
        let asked = window.update(cx, |_, window, cx| {
            window.prompt(PromptLevel::Warning, question, None, &[yes, "Cancel"], cx)
        });
        let Ok(answer) = asked else {
            return;
        };
        cx.spawn(async move |this, cx| {
            if matches!(answer.await, Ok(0))
                && let Some(this) = this.upgrade()
            {
                this.update(cx, then);
            }
        })
        .detach();
    }

    /// Saves the overlay to the project file last saved or opened, or, with `ask` or none
    /// yet, to one the system dialog picks.
    ///
    /// # Arguments
    ///
    /// * `ask` - Whether to pick the file even when one was saved or opened.
    /// * `cx` - Binary context.
    pub fn save_project(&mut self, ask: bool, cx: &mut Context<'_, Self>) {
        if let (Some(path), false) = (self.project.clone(), ask) {
            self.save_to(path, cx);
            return;
        }
        let Some(loaded) = self.loaded.clone() else {
            self.set_status("open a binary first".to_owned(), cx);
            return;
        };
        let dir = self
            .project
            .as_deref()
            .or(Some(loaded.path.as_path()))
            .and_then(Path::parent)
            .map_or_else(|| PathBuf::from("."), Path::to_path_buf);
        let stem = loaded
            .path
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy();
        let answer = cx.prompt_for_new_path(&dir, Some(&format!("{stem}.json")));
        self.on_dialog(answer, Self::save_to, cx);
    }

    /// Writes the overlay to the project file at `path` in the background; once written,
    /// what was saved is what the title compares against.
    ///
    /// # Arguments
    ///
    /// * `path` - The project file.
    /// * `cx` - Binary context.
    fn save_to(&mut self, path: PathBuf, cx: &mut Context<'_, Self>) {
        let file = path.clone();
        let label = format!("Saving project {}", file_name(&path));
        self.run(
            label,
            move |loaded| save_project_blocking(loaded, &file),
            move |binary, base, out, cx| match out {
                Ok(()) => {
                    let status = format!("saved project {}", path.display());
                    let same = binary.loaded.as_ref();
                    if same.is_some_and(|now| Arc::ptr_eq(&now.program, &base.program)) {
                        binary.saved = base.fingerprint;
                        binary.project = Some(path);
                    }
                    binary.set_status(status, cx);
                }
                Err(err) => binary.set_status(format!("project not saved: {err:#}"), cx),
            },
            cx,
        );
    }
}

/// Registers the project actions on `workspace`, each on `binary`.
///
/// # Arguments
///
/// * `workspace` - The workspace the actions dispatch in.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let (open, save, save_as) = (binary.clone(), binary.clone(), binary.clone());
    workspace
        .register_action(move |_, _: &OpenProject, window, cx| {
            let window = window.window_handle();
            open.update(cx, |binary, cx| binary.prompt_open_project(window, cx));
        })
        .register_action(move |_, _: &SaveProject, _, cx| {
            save.update(cx, |binary, cx| binary.save_project(false, cx));
        })
        .register_action(move |_, _: &SaveProjectAs, _, cx| {
            save_as.update(cx, |binary, cx| binary.save_project(true, cx));
        });
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

/// The system file dialog's options for one file, as the app asks for every file it opens.
pub(crate) const ONE_FILE: PathPromptOptions = PathPromptOptions {
    files: true,
    directories: false,
    multiple: false,
    prompt: None,
};

/// Opens the system file dialog as `options` say: the one way the app asks for paths.
///
/// # Arguments
///
/// * `options` - What the dialog picks; [`ONE_FILE`] for a file to open.
/// * `cx` - Application context.
///
/// # Returns
///
/// The dialog's answer: the chosen paths, `None` when it was cancelled, or why it failed.
pub(crate) fn ask_paths(
    options: PathPromptOptions,
    cx: &App,
) -> oneshot::Receiver<anyhow::Result<Option<Vec<PathBuf>>>> {
    cx.prompt_for_paths(options)
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
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::sync::Arc;

    use borer_engine::analysis::edit::Edit;
    use borer_engine::analysis::render::{FunctionRows, LeftOut};
    use gpui::{
        AnyWindowHandle, AppContext as _, Entity, SharedString, TestAppContext, VisualTestContext,
    };
    use ui::Color;

    use super::{Binary, STILL_READING, UNSAVED};
    use crate::app_view::tests::sample;
    use crate::worker::LoadedBinary;
    use crate::worker::tests::{HELPER, scratch, tiny_pe};

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
            notes: Vec::new(),
            identity: String::new(),
            fingerprint: sample.fingerprint,
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
        let open = |path: &PathBuf, cx: &mut TestAppContext| {
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

    /// A second edit asked while the first still runs is refused, the status line saying
    /// which runs; only the first lands, and once it did an edit runs again.
    ///
    /// # Panics
    ///
    /// Panics if the second edit is not refused, lands, or the reason is not said.
    #[gpui::test]
    fn a_second_edit_while_one_runs_is_refused_with_the_reason(cx: &mut TestAppContext) {
        use crate::app_view::tests::{CALLEE, CALLER};
        crate::app_view::tests::init(cx);
        let binary = cx.new(|cx| Binary::new(cx));
        binary.update(cx, |binary, cx| binary.finish_load(Ok(sample()), cx));
        let rename = |at: u64, name: &str| {
            vec![Edit::Name {
                at,
                name: name.to_owned(),
            }]
        };
        binary.update(cx, |binary, cx| {
            binary.edit(rename(CALLER, "first"), cx);
            binary.edit(rename(CALLEE, "second"), cx);
        });
        let status = binary.read_with(cx, |binary, _| binary.status().to_owned());
        assert_eq!(
            status,
            "Renaming 0x1030 refused: Renaming 0x1000 still runs; do it again once it ends"
        );
        cx.run_until_parked();
        let names = |cx: &mut TestAppContext| {
            binary.read_with(cx, |binary, _| {
                let overlay = &binary.loaded().unwrap().overlay;
                (
                    overlay.names.get(&CALLER).cloned(),
                    overlay.names.get(&CALLEE).cloned(),
                )
            })
        };
        assert_eq!(names(cx), (Some("first".to_owned()), None));
        binary.update(cx, |binary, cx| binary.edit(rename(CALLEE, "second"), cx));
        cx.run_until_parked();
        assert_eq!(names(cx).1, Some("second".to_owned()));
    }

    /// Returns a binary in a fresh window over an in-memory database, its loads reading no
    /// packs or symbol cache of the machine's, and the window.
    fn binary(cx: &mut TestAppContext) -> (Entity<Binary>, &mut VisualTestContext) {
        cx.update(|cx| {
            cx.set_global(db::AppDatabase::test_new());
            cx.set_global(crate::stored::FixedSources::default());
        });
        let cx = cx.add_empty_window();
        (cx.new(|cx| Binary::new(cx)), cx)
    }

    /// Returns the test window's handle.
    fn window(cx: &mut VisualTestContext) -> AnyWindowHandle {
        cx.update(|window, _| window.window_handle())
    }

    /// Opens `exe` in `binary` and waits for the load.
    fn open(binary: &Entity<Binary>, exe: &Path, cx: &mut VisualTestContext) {
        let exe = exe.to_path_buf();
        binary.update(cx, |binary, cx| binary.open_path(exe, cx));
        cx.run_until_parked();
    }

    /// Asks `binary` to open the project at `path` and waits for it, or for its question.
    fn open_project(binary: &Entity<Binary>, path: &Path, cx: &mut VisualTestContext) {
        let (path, window) = (path.to_path_buf(), window(cx));
        binary.update(cx, |binary, cx| binary.open_project(path, window, cx));
        cx.run_until_parked();
    }

    /// Returns the fingerprint of `binary`'s overlay, its title, and its status line.
    ///
    /// # Panics
    ///
    /// Panics if no binary is open.
    fn state(binary: &Entity<Binary>, cx: &mut VisualTestContext) -> (u64, String, String) {
        binary.read_with(cx, |binary, _| {
            let loaded = binary.loaded().unwrap();
            (
                loaded.fingerprint,
                binary.title(),
                binary.status().to_owned(),
            )
        })
    }

    /// Renames [`tiny_pe`]'s helper in `binary` through the edit path.
    fn rename(binary: &Entity<Binary>, cx: &mut VisualTestContext) {
        let rename = Edit::Name {
            at: HELPER,
            name: "renamed_helper".to_owned(),
        };
        binary.update(cx, |binary, cx| binary.edit(vec![rename], cx));
        cx.run_until_parked();
    }

    /// Writes [`tiny_pe`] to `dir`, renames its helper through the edit path and saves the
    /// project beside it.
    ///
    /// # Returns
    ///
    /// The binary, the project file, and the overlay's fingerprint after the rename.
    ///
    /// # Panics
    ///
    /// Panics if a step fails or the title's unsaved mark is wrong after the edit or the
    /// save.
    fn renamed_and_saved(
        binary: &Entity<Binary>,
        dir: &Path,
        cx: &mut VisualTestContext,
    ) -> (PathBuf, PathBuf, u64) {
        let exe = dir.join("tiny.exe");
        std::fs::write(&exe, tiny_pe()).unwrap();
        open(binary, &exe, cx);
        assert!(!state(binary, cx).1.contains(UNSAVED));
        rename(binary, cx);
        let (edited, title, status) = state(binary, cx);
        assert!(title.contains(UNSAVED), "{title}: {status}");
        let project = dir.join("tiny.json");
        let file = project.clone();
        binary.update(cx, |binary, cx| binary.save_to(file, cx));
        cx.run_until_parked();
        let (_, title, status) = state(binary, cx);
        assert!(!title.contains(UNSAVED), "{title}: {status}");
        (exe, project, edited)
    }

    /// A rename made through the edit path, saved and opened in a fresh state, comes back
    /// as the same overlay; the title marks the edit unsaved until the save.
    ///
    /// # Panics
    ///
    /// Panics if the fingerprints differ or the unsaved mark is wrong.
    #[gpui::test]
    fn a_saved_project_opens_to_the_same_overlay(cx: &mut TestAppContext) {
        let dir = scratch("project");
        let (binary, cx) = binary(cx);
        let (exe, project, edited) = renamed_and_saved(&binary, &dir, cx);
        let fresh = cx.new(|cx| Binary::new(cx));
        open(&fresh, &exe, cx);
        open_project(&fresh, &project, cx);
        let (opened, title, status) = state(&fresh, cx);
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(opened, edited, "{status}");
        assert!(!title.contains(UNSAVED), "{title}");
    }

    /// Opening a project over edits no project file holds asks first: Cancel keeps the
    /// edits, Open replaces them with the project's.
    ///
    /// # Panics
    ///
    /// Panics if the project opens unasked, on Cancel, or not on Open.
    #[gpui::test]
    fn a_project_over_unsaved_edits_asks_first(cx: &mut TestAppContext) {
        let dir = scratch("unsaved");
        let (binary, cx) = binary(cx);
        let (_, project, edited) = renamed_and_saved(&binary, &dir, cx);
        let again = Edit::Name {
            at: HELPER,
            name: "renamed_again".to_owned(),
        };
        binary.update(cx, |binary, cx| binary.edit(vec![again], cx));
        cx.run_until_parked();
        let (unsaved, ..) = state(&binary, cx);
        assert_ne!(unsaved, edited);
        for (answer, want) in [("Cancel", unsaved), ("Open", edited)] {
            open_project(&binary, &project, cx);
            assert!(cx.has_pending_prompt(), "{answer}");
            cx.simulate_prompt_answer(answer);
            cx.run_until_parked();
            assert_eq!(state(&binary, cx).0, want, "{answer}");
        }
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// A project saved for another build is refused in the engine's words with a choice to
    /// force it; forcing admits the bytes that were refused, though the file changed since,
    /// and the next save asks where to write.
    ///
    /// # Panics
    ///
    /// Panics if the project opens unforced, no choice is offered, force reads the file
    /// again, or the forced file stays the save target.
    #[gpui::test]
    fn another_builds_project_is_refused_until_forced(cx: &mut TestAppContext) {
        let dir = scratch("foreign");
        let (binary, cx) = binary(cx);
        let (_, project, edited) = renamed_and_saved(&binary, &dir, cx);
        let rebuilt = dir.join("rebuilt.exe");
        let mut bytes = tiny_pe();
        if let Some(last) = bytes.last_mut() {
            *last = 0x90;
        }
        std::fs::write(&rebuilt, bytes).unwrap();
        let other = cx.new(|cx| Binary::new(cx));
        open(&other, &rebuilt, cx);
        let (loaded, ..) = state(&other, cx);
        open_project(&other, &project, cx);
        let (unforced, _, refused) = state(&other, cx);
        assert_eq!(unforced, loaded);
        assert!(
            refused.starts_with("project refused: the project was saved for another build"),
            "{refused}"
        );
        std::fs::write(&project, b"not a project").unwrap();
        assert!(cx.has_pending_prompt());
        cx.simulate_prompt_answer("Force");
        cx.run_until_parked();
        let (forced, _, said) = state(&other, cx);
        let target = other.read_with(cx, |binary, _| binary.project.clone());
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(forced, edited, "{said}");
        assert!(said.contains("# forced"), "{said}");
        assert_eq!(target, None);
    }
}
