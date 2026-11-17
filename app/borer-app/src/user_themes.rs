//! The person's themes: every `*.json` theme family in the themes folder of the app's config
//! directory, read in the background at start and read again when one changes on disk.
//!
//! This follows Zed's own `load_user_themes_in_background` and `watch_themes` (in the `zed`
//! crate, which is not a library). Each file is opened once and read through that handle
//! to at most [`MAX_THEME_BYTES`], then parsed and refined on the background executor; only
//! registering the result runs on the UI thread. A theme name is held by one file: a file
//! naming one of the app's own themes or a theme another file holds is refused, as an
//! import is ([`claim`]). A file deleted takes its themes with it. A file that is refused,
//! does not read or does not parse is a notification naming it and why; the app goes on
//! without it.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{Read as _, Seek as _, SeekFrom};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use anyhow::Context as _;
use futures::StreamExt as _;
use gpui::{App, AsyncApp, Global, SharedString};
use theme::{ThemeFamily, ThemeRegistry};
use theme_settings::{ThemeFamilyContent, deserialize_user_theme, refine_theme_family};
use workspace::notifications::NotificationId;

use crate::app_settings::check_path;
use crate::shell::{dismiss_app_notice, show_app_notice};

/// Most bytes a theme file may hold before the app refuses to read it.
pub const MAX_THEME_BYTES: u64 = 4 << 20;

/// Most entries the themes folder may hold, and most theme files one change may touch.
///
/// With more at start, or in one change for the watcher, none is read and a notification
/// says why.
pub const MAX_THEME_ENTRIES: usize = 1024;

/// How long the folder's watcher gathers changes before it reports them, as Zed's does.
const WATCH_LATENCY: Duration = Duration::from_millis(100);

/// The theme file each theme read from the themes folder or imported came from, by name.
#[derive(Debug, Default)]
struct ThemeFiles(BTreeMap<SharedString, PathBuf>);

impl Global for ThemeFiles {}

/// Reads every theme file of the themes folder in the background, then watches it.
///
/// The folder is created when it is missing. Each file that changes is read again and the
/// themes of each file deleted are dropped; the shown theme is applied again after each
/// change, so one the settings name shows once it loads.
///
/// # Arguments
///
/// * `cx` - Application context, Zed's file system and theme registry already set.
pub(crate) fn load_and_watch(cx: &mut App) {
    let fs = <dyn fs::Fs>::global(cx);
    cx.spawn(async move |cx| {
        let dir = &crate::app_dirs::themes_dir();
        match theme_paths(fs.as_ref(), dir).await {
            Ok(found) => {
                for path in &found {
                    load(&fs, path, cx).await;
                }
                cx.update(theme_settings::reload_theme);
            }
            Err(err) => cx.update(|cx| notice(dir, Err(&err), cx)),
        }
        let (mut events, _watcher) = fs.watch(dir, WATCH_LATENCY).await;
        while let Some(events) = events.next().await {
            let changed: BTreeSet<_> = (events.into_iter().map(|event| event.path))
                .filter(|path| is_theme_path(path))
                .collect();
            if changed.len() > MAX_THEME_ENTRIES {
                let why = anyhow::anyhow!(
                    "{} theme files changed at once, over the {MAX_THEME_ENTRIES} the app reads",
                    changed.len()
                );
                cx.update(|cx| notice(dir, Err(&why), cx));
                continue;
            }
            let mut touched = false;
            for path in &changed {
                touched |= match fs.metadata(path).await {
                    Ok(Some(meta)) if meta.is_dir => false,
                    Ok(None) => cx.update(|cx| {
                        notice(path, Ok(()), cx);
                        unregister(path, cx)
                    }),
                    Ok(Some(_)) | Err(_) => load(&fs, path, cx).await,
                };
            }
            if touched {
                cx.update(theme_settings::reload_theme);
            }
        }
    })
    .detach();
}

/// Returns the theme files of `dir`, sorted, after creating `dir` when nothing is there.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `dir` - The themes folder.
///
/// # Errors
///
/// Returns an error when `dir` is not a folder, cannot be made or listed, or holds over
/// [`MAX_THEME_ENTRIES`] entries.
async fn theme_paths(fs: &dyn fs::Fs, dir: &Path) -> anyhow::Result<Vec<PathBuf>> {
    let shown = dir.display();
    let meta = fs.metadata(dir).await;
    match meta.with_context(|| format!("stating {shown}"))? {
        Some(meta) if !meta.is_dir => anyhow::bail!("{shown} is not a folder"),
        Some(_) => {}
        None => fs
            .create_dir(dir)
            .await
            .with_context(|| format!("creating {shown}"))?,
    }
    let mut entries = fs
        .read_dir(dir)
        .await
        .with_context(|| format!("listing {shown}"))?;
    let (mut found, mut listed) = (Vec::new(), 0usize);
    while let Some(entry) = entries.next().await {
        listed += 1;
        if listed > MAX_THEME_ENTRIES {
            anyhow::bail!("{shown} holds over {MAX_THEME_ENTRIES} entries; no theme was read");
        }
        let path = entry.with_context(|| format!("listing {shown}"))?;
        if is_theme_path(&path) {
            found.push(path);
        }
    }
    found.sort();
    Ok(found)
}

/// Returns whether `path` names a theme file: its extension is `json`, in any case.
///
/// # Arguments
///
/// * `path` - The path.
#[must_use]
pub(crate) fn is_theme_path(path: &Path) -> bool {
    path.extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("json"))
}

/// Reads the file at `path` through `fs` once [`check_path`] lets the path through: one
/// open, whose handle says the length, and a read of at most [`MAX_THEME_BYTES`] and one
/// byte from it.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `path` - The theme file.
///
/// # Errors
///
/// Returns an error naming the path when it is refused, does not open, is not a file the
/// handle can measure, holds or grows over [`MAX_THEME_BYTES`], or does not read.
pub(crate) async fn read_capped(fs: &dyn fs::Fs, path: &Path) -> anyhow::Result<Vec<u8>> {
    check_path(path, MAX_THEME_BYTES)?;
    let shown = path.display();
    let mut file = fs
        .open_sync(path)
        .await
        .with_context(|| format!("opening {shown}"))?;
    let len =
        (file.seek(SeekFrom::End(0))).with_context(|| format!("{shown} is not a regular file"))?;
    if len > MAX_THEME_BYTES {
        anyhow::bail!("{shown} holds {len} bytes, over the {MAX_THEME_BYTES} the app reads");
    }
    file.rewind().with_context(|| format!("reading {shown}"))?;
    let mut bytes = Vec::with_capacity(usize::try_from(len).unwrap_or_default());
    (file.take(MAX_THEME_BYTES.saturating_add(1)))
        .read_to_end(&mut bytes)
        .with_context(|| format!("reading {shown}"))?;
    if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > MAX_THEME_BYTES {
        anyhow::bail!("{shown} grew past the {MAX_THEME_BYTES} bytes the app reads");
    }
    Ok(bytes)
}

/// Returns the theme family `bytes`, read from `path`, hold.
///
/// # Arguments
///
/// * `path` - The file the bytes were read from, to name.
/// * `bytes` - The file's bytes.
///
/// # Errors
///
/// Returns an error naming the path when the bytes do not parse as a theme family.
pub(crate) fn parse_theme(path: &Path, bytes: &[u8]) -> anyhow::Result<ThemeFamilyContent> {
    deserialize_user_theme(bytes)
        .with_context(|| format!("{} is not a theme family", path.display()))
}

/// Refuses theme `names` for the file at `path` when one is named twice, is one of the
/// app's own themes, or is held by another file: the one rule the themes folder and an
/// import share.
///
/// # Arguments
///
/// * `names` - The theme names the file holds.
/// * `path` - The theme file, in the themes folder.
/// * `cx` - Application context reading the registry.
///
/// # Errors
///
/// Returns an error naming the theme, and the file holding it when one does.
pub(crate) fn claim(names: &[SharedString], path: &Path, cx: &App) -> anyhow::Result<()> {
    let registry = ThemeRegistry::global(cx);
    let owners = cx.try_global::<ThemeFiles>();
    for (i, name) in names.iter().enumerate() {
        if names.iter().take(i).any(|earlier| earlier == name) {
            anyhow::bail!("{} names the theme {name} twice", path.display());
        }
        match owners.and_then(|owners| owners.0.get(name)) {
            Some(owner) if owner == path => {}
            Some(owner) => {
                anyhow::bail!("a theme named {name} is already in {}", owner.display())
            }
            None if registry.get(name).is_ok() => {
                anyhow::bail!("a theme named {name} is one of the app's own")
            }
            None => {}
        }
    }
    Ok(())
}

/// Registers `family`, read from the theme file at `path`, once [`claim`] lets its names
/// through, dropping the themes the file held before and no longer does.
///
/// # Arguments
///
/// * `path` - The theme file, in the themes folder.
/// * `family` - Its theme family, refined.
/// * `cx` - Application context.
///
/// # Errors
///
/// As [`claim`], with nothing registered.
pub(crate) fn register(path: &Path, family: ThemeFamily, cx: &mut App) -> anyhow::Result<()> {
    let names: Vec<SharedString> = family.themes.iter().map(|t| t.name.clone()).collect();
    claim(&names, path, cx)?;
    let stale: Vec<_> = owned_by(path, cx)
        .into_iter()
        .filter(|name| !names.contains(name))
        .collect();
    let registry = ThemeRegistry::global(cx);
    registry.remove_user_themes(&stale);
    registry.insert_theme_families([family]);
    let owners = &mut cx.default_global::<ThemeFiles>().0;
    owners.retain(|_, owner| owner != path);
    owners.extend(names.into_iter().map(|name| (name, path.to_owned())));
    Ok(())
}

/// Drops the themes the deleted theme file at `path` held.
///
/// # Arguments
///
/// * `path` - The theme file.
/// * `cx` - Application context.
///
/// # Returns
///
/// `true` when the file held a theme.
fn unregister(path: &Path, cx: &mut App) -> bool {
    let names = owned_by(path, cx);
    ThemeRegistry::global(cx).remove_user_themes(&names);
    cx.default_global::<ThemeFiles>()
        .0
        .retain(|_, owner| owner != path);
    !names.is_empty()
}

/// Returns the names of the themes the file at `path` holds.
///
/// # Arguments
///
/// * `path` - The theme file.
/// * `cx` - Application context.
fn owned_by(path: &Path, cx: &App) -> Vec<SharedString> {
    let owners = cx.try_global::<ThemeFiles>().map(|owners| &owners.0);
    let held = owners
        .into_iter()
        .flatten()
        .filter(|(_, owner)| *owner == path);
    held.map(|(name, _)| name.clone()).collect()
}

/// Reads the theme file at `path` on the background executor and registers its family,
/// saying why in a notification when it cannot, and taking back an earlier notification of
/// that file when it can.
///
/// # Arguments
///
/// * `fs` - Zed's file system.
/// * `path` - The theme file.
/// * `cx` - Async application context.
///
/// # Returns
///
/// `true` when the family was registered.
async fn load(fs: &Arc<dyn fs::Fs>, path: &Path, cx: &mut AsyncApp) -> bool {
    let (fs, file) = (fs.clone(), path.to_owned());
    let read = cx.background_executor().spawn(async move {
        let bytes = read_capped(fs.as_ref(), &file).await?;
        anyhow::Ok(refine_theme_family(parse_theme(&file, &bytes)?))
    });
    let read = read.await;
    cx.update(|cx| {
        let done = read.and_then(|family| register(path, family, cx));
        notice(path, done.as_ref().map(drop), cx);
        done.is_ok()
    })
}

/// Shows a notification of why the theme file or folder at `path` did not load, or takes
/// back the one shown for it when it did.
///
/// # Arguments
///
/// * `path` - The theme file or folder.
/// * `read` - How reading it went.
/// * `cx` - Application context.
fn notice(path: &Path, read: Result<(), &anyhow::Error>, cx: &mut App) {
    let id = notice_id(path);
    match read {
        Ok(()) => dismiss_app_notice(&id, cx),
        Err(err) => show_app_notice(id, format!("theme not loaded: {err:#}").into(), cx),
    }
}

/// Returns the id of the notification of the theme file or folder at `path`, one per path.
///
/// # Arguments
///
/// * `path` - The theme file or folder.
#[must_use]
pub fn notice_id(path: &Path) -> NotificationId {
    NotificationId::named(format!("theme file {}", path.display()).into())
}
