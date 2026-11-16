//! The binary a window has open: its background load, its load status, and the status-bar
//! item that shows that status.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use gpui::{
    App, Context, Entity, Global, IntoElement, ParentElement as _, PathPromptOptions, Render,
    SharedString, Styled as _, Subscription, Task, Window,
};
use ui::{Color, Label, LabelCommon as _, LabelSize, h_flex};
use workspace::{HideStatusItem, ItemHandle, StatusItemView};

use crate::worker::{LoadedBinary, TaskEpoch, load_binary_blocking, spawn_engine};

/// Note appended to load status lines saying what this direct engine load omits.
pub const LOAD_SCOPE_NOTE: &str = "packs left out; session load path comes next";

/// The binary a window has open, or is loading, and the status line of that load.
pub struct Binary {
    /// The analyzed binary, once a load has finished.
    loaded: Option<Arc<LoadedBinary>>,
    /// What the status line leads with for [`Self::loaded`], built when it loaded.
    facts: Vec<(SharedString, Color)>,
    /// Error text of the most recent failed load.
    error: Option<String>,
    /// The file a running load reads, `None` once it finished or before any.
    reading: Option<PathBuf>,
    /// Status line the status bar shows.
    status: String,
    /// Generation and cancel flag of the running load.
    epoch: TaskEpoch,
    /// The running background load.
    load_task: Option<Task<()>>,
    /// The running file dialog.
    prompt_task: Option<Task<()>>,
}

impl std::fmt::Debug for Binary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Binary")
            .field("status", &self.status)
            .finish_non_exhaustive()
    }
}

impl Default for Binary {
    fn default() -> Self {
        Self {
            loaded: None,
            facts: Vec::new(),
            error: None,
            reading: None,
            status: format!("Open a binary ({LOAD_SCOPE_NOTE})"),
            epoch: TaskEpoch::new(),
            load_task: None,
            prompt_task: None,
        }
    }
}

impl Binary {
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

    /// Returns the file the running load reads, `None` when no load runs.
    #[must_use]
    pub fn reading(&self) -> Option<&Path> {
        self.reading.as_deref()
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
    /// binary open before it.
    ///
    /// # Arguments
    ///
    /// * `path` - File path of the binary to load.
    /// * `cx` - Binary context spawning the background task.
    pub fn open_path(&mut self, path: PathBuf, cx: &mut Context<'_, Self>) {
        self.loaded = None;
        self.facts.clear();
        self.error = None;
        let (ticket, worker_cancel) = self.epoch.begin();
        let check_cancel = worker_cancel.clone();
        self.status = format!("loading {} ({LOAD_SCOPE_NOTE})", path.display());
        self.reading = Some(path.clone());
        cx.notify();
        let bg = spawn_engine(cx, move || {
            worker_cancel.within(|| load_binary_blocking(path))
        });
        self.load_task = Some(cx.spawn(async move |this, cx| {
            let result = bg.await;
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |binary, cx| {
                if binary.epoch.is_current(ticket, &check_cancel) {
                    binary.finish_load(result, cx);
                }
            });
        }));
    }

    /// Applies the result of a background load.
    ///
    /// # Arguments
    ///
    /// * `result` - Outcome of [`load_binary_blocking`].
    /// * `cx` - Binary context.
    fn finish_load(
        &mut self,
        result: anyhow::Result<Arc<LoadedBinary>>,
        cx: &mut Context<'_, Self>,
    ) {
        self.reading = None;
        match result {
            Ok(loaded) => {
                self.status = format!("{} ({LOAD_SCOPE_NOTE})", loaded.path.display());
                let program = &loaded.program;
                let kind = format!("{} {}", program.arch.name(), program.format.name());
                let count = loaded.initial_rows.counts();
                self.facts = vec![
                    (kind.into(), Color::Muted),
                    (count.into(), Color::Placeholder),
                ];
                self.loaded = Some(loaded);
            }
            Err(err) => {
                let msg = format!("{err:#}");
                self.status = format!("load failed: {msg}");
                self.error = Some(msg);
            }
        }
        cx.notify();
    }
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

    /// Returns the line's text: the settings notice, if any, then the binary's status.
    ///
    /// # Arguments
    ///
    /// * `cx` - Application context reading the binary and the notice.
    #[must_use]
    pub fn text(&self, cx: &App) -> String {
        let status = self.binary.read(cx).status();
        match cx.try_global::<SettingsNotice>().and_then(|n| n.0.as_ref()) {
            Some(notice) => format!("{notice}; {status}"),
            None => status.to_owned(),
        }
    }
}

impl Render for StatusLine {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let label =
            |text: SharedString, color| Label::new(text).size(LabelSize::Small).color(color);
        let facts = self.binary.read(cx).facts().iter();
        h_flex()
            .gap_3()
            .children(facts.map(|(text, color)| label(text.clone(), *color)))
            .child(label(self.text(cx).into(), Color::Placeholder))
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
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::render::{FunctionRows, LeftOut};
    use gpui::{AppContext as _, SharedString, TestAppContext};
    use ui::Color;

    use super::Binary;
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
        let binary = cx.new(|_| Binary::default());
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
}
