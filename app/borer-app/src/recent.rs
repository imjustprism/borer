//! The binaries opened last, kept in Zed's key-value store under the app's data directory,
//! and the picker that opens one of them.
//!
//! Each is kept with the engine's architecture and format as the load read them, so the
//! start tab lists them without reading a file.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Context as _;
use db::kvp::KeyValueStore;
use gpui::{App, AppContext as _, Context, DismissEvent, Entity, ParentElement as _, Task, Window};
use picker::{Picker, PickerDelegate};
use ui::{Label, ListItem, ListItemSpacing, Toggleable as _};
use workspace::Workspace;

use crate::actions::OpenRecent;
use crate::binary::Binary;
use crate::stored::{Key, SCOPE};

/// Most binaries the list keeps.
pub const RECENT_MAX: usize = 10;

/// Most binaries the start tab shows, each with its digit key.
pub const SHOWN_MAX: usize = 5;

/// A binary opened before: its path and what the engine said it is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecentBinary {
    /// The path it was opened from.
    pub path: PathBuf,
    /// The engine's architecture and format of it, as `x86-64 PE`.
    pub kind: String,
}

impl RecentBinary {
    /// Returns the file name, the whole path when it has none.
    #[must_use]
    pub fn name(&self) -> String {
        file_name(&self.path)
    }

    /// Returns the folder the binary is in, empty when the path has none.
    #[must_use]
    pub fn folder(&self) -> String {
        self.path
            .parent()
            .map(|dir| dir.display().to_string())
            .unwrap_or_default()
    }
}

/// Returns the file name of `path`, the whole path when it has none.
///
/// # Arguments
///
/// * `path` - A binary's path.
#[must_use]
pub fn file_name(path: &Path) -> String {
    path.file_name().map_or_else(
        || path.display().to_string(),
        |name| name.to_string_lossy().into_owned(),
    )
}

/// Returns the binaries opened last, the newest first, at most [`RECENT_MAX`].
///
/// # Arguments
///
/// * `cx` - Application context reading the store.
///
/// # Errors
///
/// Returns an error when the store cannot be read or its record does not parse.
pub fn read(cx: &App) -> anyhow::Result<Vec<RecentBinary>> {
    parse(
        KeyValueStore::global(cx)
            .scoped(SCOPE)
            .read(Key::RecentBinaries.name())?,
    )
}

/// Returns the list a stored record holds, empty when there is none.
///
/// # Arguments
///
/// * `text` - The record, `None` when there is none.
///
/// # Errors
///
/// Returns an error when the record does not parse.
fn parse(text: Option<String>) -> anyhow::Result<Vec<RecentBinary>> {
    let Some(text) = text else {
        return Ok(Vec::new());
    };
    let pairs: Vec<(PathBuf, String)> =
        serde_json::from_str(&text).context("parsing the app's recent binaries")?;
    let mut list: Vec<RecentBinary> = pairs
        .into_iter()
        .map(|(path, kind)| RecentBinary { path, kind })
        .collect();
    list.truncate(RECENT_MAX);
    Ok(list)
}

/// Returns `list` with `opened` first and its path nowhere else, at most [`RECENT_MAX`].
///
/// A path that is not UTF-8 cannot be written to the store, so it is left out rather than
/// keep every later write of the list from landing.
///
/// # Arguments
///
/// * `list` - The binaries opened last, the newest first.
/// * `opened` - The binary just opened.
#[must_use]
pub fn remembered(mut list: Vec<RecentBinary>, opened: RecentBinary) -> Vec<RecentBinary> {
    if opened.path.to_str().is_none() {
        return list;
    }
    list.retain(|old| old.path != opened.path);
    list.insert(0, opened);
    list.truncate(RECENT_MAX);
    list
}

/// Writes `list` to the store in the background.
///
/// # Arguments
///
/// * `list` - The binaries opened last, the newest first.
/// * `cx` - Application context.
///
/// # Returns
///
/// The write, which fails when the store refuses it.
pub fn write(list: &[RecentBinary], cx: &App) -> Task<anyhow::Result<()>> {
    let text = encode(list);
    let kvp = KeyValueStore::global(cx);
    cx.background_spawn(async move {
        kvp.scoped(SCOPE)
            .write(Key::RecentBinaries.name().to_owned(), text?)
            .await
    })
}

/// Returns the store's record of `list`.
///
/// # Arguments
///
/// * `list` - The binaries opened last, the newest first.
///
/// # Errors
///
/// Returns an error when a path is not UTF-8, which [`remembered`] never adds.
fn encode(list: &[RecentBinary]) -> serde_json::Result<String> {
    let pairs: Vec<(&Path, &str)> = list
        .iter()
        .map(|recent| (recent.path.as_path(), recent.kind.as_str()))
        .collect();
    serde_json::to_string(&pairs)
}

/// Registers [`OpenRecent`] on `workspace`, its picker opening the choice in `binary`.
///
/// # Arguments
///
/// * `workspace` - The workspace the action dispatches in.
/// * `binary` - The window's binary.
pub fn register(workspace: &mut Workspace, binary: &Entity<Binary>) {
    let binary = binary.clone();
    workspace.register_action(move |workspace, _: &OpenRecent, window, cx| {
        toggle(workspace, binary.clone(), window, cx);
    });
}

/// What the picker lists and which one is highlighted.
#[derive(Debug)]
pub struct RecentBinaries {
    /// The binary a choice opens in.
    binary: Entity<Binary>,
    /// The binaries opened last, the newest first, as `binary` holds them.
    list: Vec<RecentBinary>,
    /// Indices into [`Self::list`] the query matches, in order.
    matches: Vec<usize>,
    /// Index into [`Self::matches`] of the highlighted row.
    selected: usize,
}

impl RecentBinaries {
    /// Returns the picker's rows over the binaries `binary` opened last, all matching.
    ///
    /// # Arguments
    ///
    /// * `binary` - The binary a choice opens in.
    /// * `cx` - Application context reading it.
    #[must_use]
    pub fn new(binary: Entity<Binary>, cx: &App) -> Self {
        let list = binary.read(cx).recent().to_vec();
        Self {
            binary,
            matches: (0..list.len()).collect(),
            list,
            selected: 0,
        }
    }

    /// Returns the paths the query matches, in order.
    #[must_use]
    pub fn shown(&self) -> Vec<&Path> {
        self.matches
            .iter()
            .filter_map(|&ix| self.list.get(ix))
            .map(|recent| recent.path.as_path())
            .collect()
    }
}

/// Opens the recent binaries picker over `workspace`.
///
/// # Arguments
///
/// * `workspace` - The workspace the picker opens in.
/// * `binary` - The binary a choice opens in.
/// * `window` - Window the workspace is in.
/// * `cx` - Workspace context.
pub fn toggle(
    workspace: &mut Workspace,
    binary: Entity<Binary>,
    window: &mut Window,
    cx: &mut Context<'_, Workspace>,
) {
    let delegate = RecentBinaries::new(binary, cx);
    workspace.toggle_modal(window, cx, |window, cx| {
        Picker::uniform_list(delegate, window, cx)
    });
}

impl PickerDelegate for RecentBinaries {
    type ListItem = ListItem;

    fn name() -> &'static str {
        "RecentBinaries"
    }

    fn placeholder_text(&self, _window: &mut Window, _cx: &mut App) -> Arc<str> {
        "Open a recent binary".into()
    }

    fn selected_index(&self) -> usize {
        self.selected
    }

    fn match_count(&self) -> usize {
        self.matches.len()
    }

    fn set_selected_index(
        &mut self,
        ix: usize,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) {
        self.selected = ix;
    }

    fn update_matches(
        &mut self,
        query: String,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> Task<()> {
        let query = query.to_lowercase();
        self.matches = self
            .list
            .iter()
            .enumerate()
            .filter(|(_, recent)| {
                let path = recent.path.to_string_lossy().to_lowercase();
                path.contains(&query)
            })
            .map(|(ix, _)| ix)
            .collect();
        self.selected = 0;
        Task::ready(())
    }

    fn confirm(
        &mut self,
        _secondary: bool,
        _window: &mut Window,
        cx: &mut Context<'_, Picker<Self>>,
    ) {
        let chosen = self
            .matches
            .get(self.selected)
            .and_then(|&ix| self.list.get(ix));
        if let Some(recent) = chosen {
            let path = recent.path.clone();
            self.binary
                .update(cx, |binary, cx| binary.open_path(path, cx));
        }
        cx.emit(DismissEvent);
    }

    fn dismissed(&mut self, _window: &mut Window, _cx: &mut Context<'_, Picker<Self>>) {}

    fn render_match(
        &self,
        ix: usize,
        selected: bool,
        _window: &mut Window,
        _cx: &mut Context<'_, Picker<Self>>,
    ) -> Option<Self::ListItem> {
        let recent = self.list.get(*self.matches.get(ix)?)?;
        let text = format!("{}  {}", recent.path.display(), recent.kind);
        Some(
            ListItem::new(ix)
                .inset(true)
                .spacing(ListItemSpacing::Sparse)
                .toggle_state(selected)
                .child(Label::new(text)),
        )
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::{RECENT_MAX, RecentBinary, encode, parse, remembered};

    /// Returns the recent binary `n`, a PE.
    fn binary(n: usize) -> RecentBinary {
        RecentBinary {
            path: PathBuf::from(format!("dir/b{n}.exe")),
            kind: String::from("x86-64 PE"),
        }
    }

    /// A binary opened again moves to the front once, the list keeps [`RECENT_MAX`], and a
    /// longer record read back is cut to them.
    ///
    /// # Panics
    ///
    /// Panics if an entry repeats, the order is wrong or the cap does not hold.
    #[test]
    fn the_newest_binary_leads_once_and_the_list_is_capped() {
        let list: Vec<RecentBinary> = (0..RECENT_MAX).map(binary).collect();
        let again = remembered(list.clone(), binary(3));
        assert_eq!(again.len(), RECENT_MAX);
        assert_eq!(again.first(), Some(&binary(3)));
        assert_eq!(again.iter().filter(|b| **b == binary(3)).count(), 1);
        let fresh = remembered(list, binary(RECENT_MAX));
        assert_eq!(fresh.len(), RECENT_MAX);
        assert_eq!(fresh.last(), Some(&binary(RECENT_MAX - 2)));
        let long: Vec<(PathBuf, String)> = (0..RECENT_MAX + 3)
            .map(|n| (binary(n).path, binary(n).kind))
            .collect();
        let read = parse(Some(serde_json::to_string(&long).unwrap())).unwrap();
        assert_eq!(read.len(), RECENT_MAX);
        assert_eq!(read.first(), Some(&binary(0)));
        assert!(parse(None).unwrap().is_empty());
        assert!(parse(Some(String::from("not json"))).is_err());
    }

    /// A row shows the file name and its folder.
    ///
    /// # Panics
    ///
    /// Panics if the name or the folder is wrong.
    #[test]
    fn a_row_splits_the_name_from_the_folder() {
        let b = binary(1);
        assert_eq!(b.name(), "b1.exe");
        assert_eq!(b.folder(), PathBuf::from("dir").display().to_string());
    }

    /// Returns a path that is not UTF-8.
    #[cfg(windows)]
    fn not_utf8() -> PathBuf {
        use std::os::windows::ffi::OsStringExt as _;
        PathBuf::from(std::ffi::OsString::from_wide(&[0x61, 0xd800, 0x2e, 0x62]))
    }

    /// Returns a path that is not UTF-8.
    #[cfg(unix)]
    fn not_utf8() -> PathBuf {
        use std::os::unix::ffi::OsStrExt as _;
        PathBuf::from(std::ffi::OsStr::from_bytes(b"x\xff.bin"))
    }

    /// A path that is not UTF-8 is not added, so the list stays writable and the next
    /// binary is kept.
    ///
    /// # Panics
    ///
    /// Panics if the path is added or the list does not encode.
    #[test]
    fn a_path_that_is_not_utf8_leaves_the_list_writable() {
        let odd = RecentBinary {
            path: not_utf8(),
            kind: String::from("x86-64 PE"),
        };
        let list = remembered(Vec::new(), odd);
        assert!(list.is_empty());
        let list = remembered(list, binary(1));
        assert_eq!(list, vec![binary(1)]);
        let read = parse(Some(encode(&list).unwrap())).unwrap();
        assert_eq!(read, list);
    }
}
