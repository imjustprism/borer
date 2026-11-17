//! Importing a theme file, after a report of how it keeps the theme contract.
//!
//! A file the file dialog picks or one dropped on a tab is read as the themes folder reads
//! a file, each of its themes is checked against the theme contract
//! ([`crate::theme_contract`]) on the background executor, and a report shows the result
//! before anything is copied.
//!
//! Import copies the file, byte for byte (a Zed theme with borer's keys added,
//! [`Origin::Zed`]), into the themes folder and registers it; it
//! never edits the file it was given and never replaces one: the copy is written beside the
//! destination and moved into place only if nothing is there. A theme name the themes
//! folder's rule refuses ([`crate::user_themes::claim`]) refuses the import.

use std::fmt;
use std::path::PathBuf;
use std::sync::Arc;

use anyhow::Context as _;
use fs::{RemoveOptions, RenameOptions};
use gpui::{
    AsyncApp, AsyncWindowContext, DismissEvent, EventEmitter, FocusHandle, Focusable, Task,
    WeakEntity,
};
use settings::Settings as _;
use theme::{Appearance, SystemAppearance, ThemeFamily};
use theme_settings::{
    ThemeFamilyContent, ThemeSettings, deserialize_user_theme, refine_theme_family,
};
use ui::prelude::*;
use workspace::{ModalView, Workspace};

use crate::app_settings::{BORER_THEME, choose_theme, save_settings};
use crate::binary::{ONE_FILE, ask_paths};
use crate::theme_contract::{Failure, check};
use crate::user_themes::{MAX_THEME_BYTES, claim, parse_theme, read_capped, register};

/// Most failure lines the report shows for one theme; the rest are counted.
const MAX_REPORT_LINES: usize = 12;

/// A theme file read for import, with each of its themes' contract failures.
pub struct Candidate {
    /// The file the theme was read from, never written.
    pub source: PathBuf,
    /// The bytes to copy: the file's as read, or for [`Origin::Zed`] the family with
    /// borer's keys.
    bytes: Vec<u8>,
    /// The file's theme family, refined.
    family: ThemeFamily,
    /// Each theme's name, appearance and the rules it breaks, in the file's order.
    pub reports: Vec<(SharedString, Appearance, Vec<Failure>)>,
    /// Each theme's name and the `borer.*` keys it takes from borer's theme, from
    /// [`borrow_borer_keys`]; empty for a file imported as it is.
    pub borrowed: Vec<(SharedString, Vec<String>)>,
}

impl fmt::Debug for Candidate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Candidate")
            .field("source", &self.source)
            .field("reports", &self.reports)
            .finish_non_exhaustive()
    }
}

/// Where a theme file comes from, which says whether it is imported as it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Origin {
    /// A file the person picked or dropped: copied byte for byte.
    File,
    /// A theme Zed has installed: each `borer.*` key it leaves unset takes borer's value
    /// ([`borrow_borer_keys`]), and the copy is the family with them.
    Zed,
}

/// Returns the candidate `bytes`, read from `source`, make: parsed, each theme checked
/// against the contract, the family refined.
///
/// # Arguments
///
/// * `source` - The file the bytes were read from.
/// * `bytes` - The file's bytes.
/// * `origin` - Where the file comes from.
///
/// # Errors
///
/// Returns an error naming the file when the bytes do not parse as a theme family or hold
/// no theme, or a Zed theme with borer's keys does not write back or writes back over
/// [`MAX_THEME_BYTES`], which the themes folder would not read.
fn candidate(source: PathBuf, bytes: Vec<u8>, origin: Origin) -> anyhow::Result<Candidate> {
    let mut content = parse_theme(&source, &bytes)?;
    if content.themes.is_empty() {
        anyhow::bail!("{} holds no theme", source.display());
    }
    let (bytes, borrowed) = match origin {
        Origin::File => (bytes, Vec::new()),
        Origin::Zed => {
            let borrowed = borrow_borer_keys(&mut content);
            let written = serde_json::to_vec_pretty(&content)
                .with_context(|| format!("writing {} with borer's keys", source.display()))?;
            let len = u64::try_from(written.len()).unwrap_or(u64::MAX);
            if len > MAX_THEME_BYTES {
                anyhow::bail!(
                    "{} with borer's keys holds {len} bytes, over the {MAX_THEME_BYTES} the app reads",
                    source.display()
                );
            }
            (written, borrowed)
        }
    };
    let failures: Vec<_> = content.themes.iter().map(check).collect();
    let family = refine_theme_family(content);
    let reports = (family.themes.iter().zip(failures))
        .map(|(theme, failures)| (theme.name.clone(), theme.appearance, failures))
        .collect();
    Ok(Candidate {
        source,
        bytes,
        family,
        reports,
        borrowed,
    })
}

/// Fills each `borer.*` syntax key the themes of `family` leave unset with the value
/// borer's theme of the same appearance gives it.
///
/// # Arguments
///
/// * `family` - The theme family, as its file writes it.
///
/// # Returns
///
/// Each theme's name and the keys it took, in the file's order; none when borer's own
/// family does not parse, which a test rules out.
pub fn borrow_borer_keys(family: &mut ThemeFamilyContent) -> Vec<(SharedString, Vec<String>)> {
    let Ok(borer) = deserialize_user_theme(BORER_THEME) else {
        return Vec::new();
    };
    let mut borrowed = Vec::new();
    for theme in &mut family.themes {
        let own = borer
            .themes
            .iter()
            .find(|b| b.appearance == theme.appearance);
        let syntax = own.into_iter().flat_map(|own| &own.style.syntax);
        let mut taken = Vec::new();
        for (key, style) in syntax.filter(|(key, _)| key.starts_with("borer.")) {
            if !theme.style.syntax.contains_key(key) {
                theme.style.syntax.insert(key.clone(), style.clone());
                taken.push(key.clone());
            }
        }
        borrowed.push((theme.name.clone().into(), taken));
    }
    borrowed
}

/// Reads the theme file at `source` and checks each of its themes against the contract,
/// on the background executor.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `source` - The theme file to import.
/// * `cx` - Application context.
///
/// # Returns
///
/// The task reading it, which fails naming the file when it is refused, does not read,
/// does not parse as a theme family, or holds no theme.
pub fn read_candidate(
    fs: Arc<dyn fs::Fs>,
    source: PathBuf,
    cx: &App,
) -> Task<anyhow::Result<Candidate>> {
    read_from(fs, source, Origin::File, cx)
}

/// Reads the theme file at `source` as one from `origin`, as [`read_candidate`] does.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `source` - The theme file to import.
/// * `origin` - Where the file comes from.
/// * `cx` - Application context.
///
/// # Returns
///
/// The task reading it, failing as [`read_candidate`]'s does.
pub fn read_from(
    fs: Arc<dyn fs::Fs>,
    source: PathBuf,
    origin: Origin,
    cx: &App,
) -> Task<anyhow::Result<Candidate>> {
    cx.background_executor().spawn(async move {
        let bytes = read_capped(fs.as_ref(), &source).await?;
        candidate(source, bytes, origin)
    })
}

/// Reads a dropped `.json` file as [`read_candidate`] does, and says whether it is a theme
/// drop.
///
/// A theme drop is one whose bytes parse as a theme family, or parse as JSON with a
/// top-level `themes` key, which is shown with why it is not one.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `source` - The dropped file.
/// * `cx` - Application context.
///
/// # Returns
///
/// The task reading it: `None` when the file is not a theme drop (it does not read, or is
/// JSON of another kind or no JSON), else the candidate or why it does not parse.
pub fn read_dropped(
    fs: Arc<dyn fs::Fs>,
    source: PathBuf,
    cx: &App,
) -> Task<Option<anyhow::Result<Candidate>>> {
    cx.background_executor().spawn(async move {
        let Ok(bytes) = read_capped(fs.as_ref(), &source).await else {
            return None;
        };
        let themed = serde_json::from_slice::<serde_json::Value>(&bytes)
            .is_ok_and(|json| json.get("themes").is_some());
        let read = candidate(source, bytes, Origin::File);
        (read.is_ok() || themed).then_some(read)
    })
}

/// Copies `candidate`'s bytes into the themes folder under its file's own name with a
/// `.json` extension, and registers its themes.
///
/// The bytes are written to a `.part` file beside the destination, which is moved into
/// place only if nothing is there, so a file that appears meanwhile is never replaced.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `candidate` - The file, from [`read_candidate`].
/// * `cx` - Async application context.
///
/// # Returns
///
/// The path the file was copied to.
///
/// # Errors
///
/// Returns an error, having left nothing in the folder, when a file of that name is there
/// (naming it), [`crate::user_themes::claim`] refuses a theme name, or the folder cannot be
/// made or the file not written or moved.
pub async fn import(
    fs: &dyn fs::Fs,
    candidate: Candidate,
    cx: &mut AsyncApp,
) -> anyhow::Result<PathBuf> {
    let source = &candidate.source;
    let mut name = source
        .file_stem()
        .with_context(|| format!("{} names no file", source.display()))?
        .to_owned();
    name.push(".json");
    let dir = &crate::app_dirs::themes_dir();
    let dest = dir.join(&name);
    let shown = dest.display();
    let there = fs.metadata(&dest).await;
    if there.with_context(|| format!("stating {shown}"))?.is_some() {
        anyhow::bail!("{shown} is already there; nothing imported");
    }
    let names: Vec<_> = candidate
        .family
        .themes
        .iter()
        .map(|t| t.name.clone())
        .collect();
    cx.update(|cx| claim(&names, &dest, cx))?;
    fs.create_dir(dir)
        .await
        .with_context(|| format!("creating {}", dir.display()))?;
    name.push(".part");
    let part = dir.join(name);
    fs.write(&part, &candidate.bytes)
        .await
        .with_context(|| format!("writing {}", part.display()))?;
    if let Err(err) = fs.rename(&part, &dest, RenameOptions::default()).await {
        let gone = RemoveOptions {
            ignore_if_not_exists: true,
            ..RemoveOptions::default()
        };
        let left = match fs.remove_file(&part, gone).await {
            Ok(()) => String::new(),
            Err(why) => format!("; {} is left: {why:#}", part.display()),
        };
        let why = format!(
            "moving {} to {shown}; nothing imported{left}",
            part.display()
        );
        return Err(err.context(why));
    }
    cx.update(|cx| register(&dest, candidate.family, cx))?;
    Ok(dest)
}

/// Opens the file dialog for a theme file and shows its import report over the workspace,
/// or why the file cannot be imported.
///
/// # Arguments
///
/// * `window` - The workspace's window.
/// * `cx` - Workspace context.
pub fn prompt(window: &mut Window, cx: &mut Context<'_, Workspace>) {
    let chosen = ask_paths(ONE_FILE, cx);
    cx.spawn_in(window, async move |workspace, cx| {
        let Ok(answer) = chosen.await else {
            return Ok(());
        };
        let path = match answer {
            Ok(Some(paths)) => paths.into_iter().next(),
            Ok(None) => None,
            Err(err) => return show(&workspace, Err(err.context("the file dialog failed")), cx),
        };
        let Some(path) = path else {
            return Ok(());
        };
        let read = cx.update(|_, cx| read_candidate(<dyn fs::Fs>::global(cx), path, cx))?;
        show(&workspace, read.await, cx)
    })
    .detach_and_log_err(cx);
}

/// Shows the import report of `read` over `workspace`.
///
/// # Arguments
///
/// * `workspace` - The workspace the report opens over.
/// * `read` - The file read for import, or why it was not.
/// * `cx` - Async window context of the workspace's window.
///
/// # Errors
///
/// Returns an error when the workspace or its window is gone.
pub fn show(
    workspace: &WeakEntity<Workspace>,
    read: anyhow::Result<Candidate>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    workspace.update_in(cx, |workspace, window, cx| {
        workspace.toggle_modal(window, cx, |_, cx| ImportReport::new(read, cx));
    })
}

/// The import report: each theme of the file with the rules it breaks, and the buttons
/// that import it.
pub struct ImportReport {
    /// The file to import; taken when an import starts.
    candidate: Option<Candidate>,
    /// The file's name, for the title.
    title: SharedString,
    /// Why the file was not read or not imported, once it was not.
    refusal: Option<SharedString>,
    /// Focus handle of the report.
    focus_handle: FocusHandle,
}

impl fmt::Debug for ImportReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ImportReport")
            .field("candidate", &self.candidate)
            .field("refusal", &self.refusal)
            .finish_non_exhaustive()
    }
}

impl ImportReport {
    /// Returns the report of `read`.
    ///
    /// # Arguments
    ///
    /// * `read` - The file read for import, or why it was not.
    /// * `cx` - Report context.
    fn new(read: anyhow::Result<Candidate>, cx: &mut Context<'_, Self>) -> Self {
        let (candidate, refusal) = match read {
            Ok(candidate) => (Some(candidate), None),
            Err(err) => (None, Some(format!("not imported: {err:#}").into())),
        };
        let title: SharedString = candidate.as_ref().map_or_else(
            || "Import a theme".into(),
            |candidate| format!("Import {}", candidate.source.display()).into(),
        );
        Self {
            candidate,
            title,
            refusal,
            focus_handle: cx.focus_handle(),
        }
    }

    /// Returns the candidate's themes and the rules each breaks, as the report shows them.
    #[must_use]
    pub fn reports(&self) -> &[(SharedString, Appearance, Vec<Failure>)] {
        self.candidate
            .as_ref()
            .map_or(&[][..], |c| c.reports.as_slice())
    }

    /// Returns why the file was not read or not imported, once it was not.
    #[must_use]
    pub fn refusal(&self) -> Option<&str> {
        self.refusal.as_deref()
    }

    /// Imports the file in the background, then selects its first theme when `use_it`
    /// says to and closes the report; a refused import stays in the report with its reason.
    ///
    /// # Arguments
    ///
    /// * `use_it` - Whether to select the file's first theme once it is imported.
    /// * `cx` - Report context.
    pub fn import(&mut self, use_it: bool, cx: &mut Context<'_, Self>) {
        let Some(candidate) = self.candidate.take() else {
            return;
        };
        let first = candidate
            .reports
            .first()
            .map(|(name, appearance, _)| (name.clone(), *appearance));
        let fs = <dyn fs::Fs>::global(cx);
        cx.spawn(async move |this, cx| {
            let done = import(fs.as_ref(), candidate, cx).await;
            let Some(this) = this.upgrade() else {
                return;
            };
            this.update(cx, |this, cx| match done {
                Ok(_) => {
                    if let Some((name, appearance)) = first.filter(|_| use_it) {
                        let system = SystemAppearance::global(cx).0;
                        let current = &ThemeSettings::get_global(cx).theme;
                        let chosen = choose_theme(current, &name, appearance, system);
                        save_settings(
                            "theme",
                            move |content| content.theme.theme = Some(chosen),
                            cx,
                        );
                    }
                    theme_settings::reload_theme(cx);
                    cx.emit(DismissEvent);
                }
                Err(err) => {
                    this.refusal = Some(format!("not imported: {err:#}").into());
                    cx.notify();
                }
            });
        })
        .detach();
    }
}

impl EventEmitter<DismissEvent> for ImportReport {}

impl ModalView for ImportReport {}

impl Focusable for ImportReport {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus_handle.clone()
    }
}

impl Render for ImportReport {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<'_, Self>) -> impl IntoElement {
        let mut body = v_flex().gap_1();
        let borrowed = self
            .candidate
            .as_ref()
            .map_or(&[][..], |c| c.borrowed.as_slice());
        for (name, _, failures) in self.reports() {
            body = body.child(Label::new(name.clone()));
            let taken = borrowed.iter().find(|(theme, _)| theme == name);
            if let Some((_, keys)) = taken.filter(|(_, keys)| !keys.is_empty()) {
                let line = format!("takes borer's value for {}", keys.join(", "));
                body = body.child(Label::new(line).size(LabelSize::Small).color(Color::Muted));
            }
            if failures.is_empty() {
                body = body.child(Label::new("keeps the contract").color(Color::Muted));
            }
            for failure in failures.iter().take(MAX_REPORT_LINES) {
                body = body.child(
                    Label::new(failure.to_string())
                        .size(LabelSize::Small)
                        .color(Color::Warning),
                );
            }
            if let Some(more) = failures
                .len()
                .checked_sub(MAX_REPORT_LINES)
                .filter(|n| *n > 0)
            {
                let line = format!("and {more} more");
                body = body.child(Label::new(line).size(LabelSize::Small).color(Color::Muted));
            }
        }
        if let Some(refusal) = &self.refusal {
            body = body.child(Label::new(refusal.clone()).color(Color::Error));
        }
        let ready = self.candidate.is_some();
        let buttons = h_flex()
            .gap_1()
            .justify_end()
            .child(
                Button::new("cancel", "Cancel").on_click(cx.listener(|_, _, _, cx| {
                    cx.emit(DismissEvent);
                })),
            )
            .child(
                Button::new("import", "Import")
                    .disabled(!ready)
                    .on_click(cx.listener(|this, _, _, cx| this.import(false, cx))),
            )
            .child(
                Button::new("import-and-use", "Import and use")
                    .disabled(!ready)
                    .on_click(cx.listener(|this, _, _, cx| this.import(true, cx))),
            );
        v_flex()
            .key_context("ImportReport")
            .track_focus(&self.focus_handle)
            .on_action(cx.listener(|this, _: &menu::Confirm, _, cx| this.import(false, cx)))
            .on_action(cx.listener(|this, _: &menu::SecondaryConfirm, _, cx| this.import(true, cx)))
            .on_action(cx.listener(|_, _: &menu::Cancel, _, cx| cx.emit(DismissEvent)))
            .elevation_3(cx)
            .w(rems(40.))
            .p_3()
            .gap_2()
            .child(Headline::new(self.title.clone()).size(HeadlineSize::Small))
            .child(body)
            .child(buttons)
    }
}
