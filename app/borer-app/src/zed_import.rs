//! Importing a theme Zed has installed.
//!
//! The theme files of Zed's themes folder and of its installed extensions are listed in a
//! picker, and the one picked goes through the import report ([`crate::theme_import`]) as
//! any theme file does.
//!
//! A Zed theme sets none of borer's own `borer.*` keys, so each one it leaves unset takes
//! the value borer's theme of the same appearance gives it
//! ([`crate::theme_import::borrow_borer_keys`]), and the report names every key taken.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use futures::StreamExt as _;
use gpui::{
    DismissEvent, Entity, EventEmitter, FocusHandle, Focusable, Task, TaskExt as _, WeakEntity,
};
use picker::{Picker, PickerDelegate};
use ui::prelude::*;
use ui::{ListItem, ListItemSpacing};
use workspace::{ModalView, Workspace};

use crate::app_dirs::{Dirs, with_host_env};
use crate::theme_import::{Origin, read_from, show};
use crate::user_themes::{MAX_THEME_ENTRIES, is_theme_path};

/// One theme file Zed has installed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZedTheme {
    /// The file.
    pub path: PathBuf,
    /// Where Zed has it: `themes folder` or the extension's folder name.
    pub from: SharedString,
}

/// Returns the theme files Zed keeps in `zed`: its themes folder's, then each installed
/// extension's `themes` folder's, each sorted by path.
///
/// At most [`MAX_THEME_ENTRIES`] entries are listed over all folders; a folder that is
/// missing or does not list adds nothing.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `zed` - Zed's directories, from [`crate::app_dirs::Env::zed`].
pub async fn zed_themes(fs: &dyn fs::Fs, zed: &Dirs) -> Vec<ZedTheme> {
    let mut budget = MAX_THEME_ENTRIES;
    let mut found = Vec::new();
    let own = list(fs, &zed.config.join("themes"), &mut budget).await;
    found.extend(
        own.into_iter()
            .filter(|p| is_theme_path(p))
            .map(|path| ZedTheme {
                path,
                from: "themes folder".into(),
            }),
    );
    let installed = zed.data.join("extensions").join("installed");
    for extension in list(fs, &installed, &mut budget).await {
        let name = extension
            .file_name()
            .map(|n| n.to_string_lossy().into_owned());
        let from: SharedString = name.unwrap_or_default().into();
        let files = list(fs, &extension.join("themes"), &mut budget).await;
        found.extend(
            files
                .into_iter()
                .filter(|p| is_theme_path(p))
                .map(|path| ZedTheme {
                    path,
                    from: from.clone(),
                }),
        );
    }
    found
}

/// Returns the entries of `dir`, sorted, taking each from `budget` and none once it is
/// spent; none when `dir` does not list.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `dir` - The folder.
/// * `budget` - Entries left to list.
async fn list(fs: &dyn fs::Fs, dir: &Path, budget: &mut usize) -> Vec<PathBuf> {
    let Ok(mut entries) = fs.read_dir(dir).await else {
        return Vec::new();
    };
    let mut found = Vec::new();
    while let Some(entry) = entries.next().await {
        let Some(left) = budget.checked_sub(1) else {
            break;
        };
        *budget = left;
        if let Ok(path) = entry {
            found.push(path);
        }
    }
    found.sort();
    found
}

/// Opens the picker over the theme files Zed has installed, once they are listed in the
/// background; the one picked opens its import report.
///
/// # Arguments
///
/// * `window` - The workspace's window.
/// * `cx` - Workspace context.
pub fn toggle(window: &mut Window, cx: &mut Context<'_, Workspace>) {
    let fs = <dyn fs::Fs>::global(cx);
    cx.spawn_in(window, async move |workspace, cx| {
        let zed = with_host_env(|env| env.zed())?;
        let themes = zed_themes(fs.as_ref(), &zed).await;
        workspace.update_in(cx, |workspace, window, cx| {
            let me = cx.entity().downgrade();
            workspace.toggle_modal(window, cx, |window, cx| {
                let delegate = ZedThemes {
                    matches: (0..themes.len()).collect(),
                    themes,
                    selected: 0,
                    workspace: me,
                    modal: cx.entity().downgrade(),
                };
                ZedPicker {
                    picker: cx.new(|cx| Picker::uniform_list(delegate, window, cx)),
                }
            });
        })
    })
    .detach_and_log_err(cx);
}

/// The modal listing the theme files Zed has installed.
#[derive(Debug)]
pub struct ZedPicker {
    /// The picker.
    picker: Entity<Picker<ZedThemes>>,
}

impl ZedPicker {
    /// Returns the picker inside the modal.
    #[must_use]
    pub const fn picker(&self) -> &Entity<Picker<ZedThemes>> {
        &self.picker
    }
}

impl EventEmitter<DismissEvent> for ZedPicker {}

impl ModalView for ZedPicker {}

impl Focusable for ZedPicker {
    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.picker.focus_handle(cx)
    }
}

impl Render for ZedPicker {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<'_, Self>) -> impl IntoElement {
        v_flex()
            .key_context("ZedThemePicker")
            .w(rems(34.))
            .child(self.picker.clone())
    }
}

/// The list of the theme files Zed has installed, each by its file name and where Zed has it.
#[derive(Debug)]
pub struct ZedThemes {
    /// Every theme file listed.
    themes: Vec<ZedTheme>,
    /// The files the query matches, as indices into [`Self::themes`].
    matches: Vec<usize>,
    /// The selected match, an index into [`Self::matches`].
    selected: usize,
    /// The workspace the import report opens over.
    workspace: WeakEntity<Workspace>,
    /// The modal, which a confirm or dismiss closes.
    modal: WeakEntity<ZedPicker>,
}

impl ZedThemes {
    /// Returns the theme files listed.
    #[must_use]
    pub fn themes(&self) -> &[ZedTheme] {
        &self.themes
    }
}

impl PickerDelegate for ZedThemes {
    type ListItem = ListItem;

    fn name() -> &'static str {
        "zed theme picker"
    }

    fn match_count(&self) -> usize {
        self.matches.len()
    }

    fn selected_index(&self) -> usize {
        self.selected
    }

    fn set_selected_index(&mut self, ix: usize, _: &mut Window, _: &mut Context<'_, Picker<Self>>) {
        self.selected = ix;
    }

    fn placeholder_text(&self, _window: &mut Window, _cx: &mut App) -> Arc<str> {
        if self.themes.is_empty() {
            "Zed has no theme installed".into()
        } else {
            "Import a theme from Zed...".into()
        }
    }

    fn update_matches(
        &mut self,
        query: String,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> Task<()> {
        let query = query.to_lowercase();
        self.matches = (self.themes.iter().enumerate())
            .filter(|(_, theme)| label(theme).to_lowercase().contains(&query))
            .map(|(i, _)| i)
            .collect();
        self.selected = 0;
        Task::ready(())
    }

    fn confirm(
        &mut self,
        _secondary: bool,
        window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) {
        let chosen = (self.matches.get(self.selected)).and_then(|&i| self.themes.get(i));
        if let (Some(theme), Some(modal)) = (chosen, self.modal.upgrade()) {
            let fs = <dyn fs::Fs>::global(cx);
            let read = read_from(fs, theme.path.clone(), Origin::Zed, cx);
            let workspace = self.workspace.clone();
            modal.update(cx, |_, cx| cx.emit(DismissEvent));
            window
                .spawn(cx, async move |cx| show(&workspace, read.await, cx))
                .detach_and_log_err(cx);
        }
    }

    fn dismissed(&mut self, _window: &mut Window, cx: &mut Context<'_, Picker<Self>>) {
        if let Some(modal) = self.modal.upgrade() {
            modal.update(cx, |_, cx| cx.emit(DismissEvent));
        }
    }

    fn render_match(
        &self,
        ix: usize,
        selected: bool,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> Option<Self::ListItem> {
        let theme = self.themes.get(*self.matches.get(ix)?)?;
        Some(
            ListItem::new(ix)
                .inset(true)
                .spacing(ListItemSpacing::Sparse)
                .toggle_state(selected)
                .child(Label::new(label(theme)))
                .end_slot(Label::new(theme.from.clone()).color(Color::Muted)),
        )
    }
}

/// Returns the name a theme file is listed by: its file name without `.json`.
///
/// # Arguments
///
/// * `theme` - The theme file.
fn label(theme: &ZedTheme) -> String {
    let stem = theme
        .path
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned());
    stem.unwrap_or_default()
}
