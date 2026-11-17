//! The app's settings over Zed's, and the theme actions that write the person's file.
//!
//! borer's theme is loaded, the app's settings are Zed's global layer, and the person's
//! settings file in the app's config directory ([`crate::app_dirs`]) is the user layer
//! over them.

use std::path::Path;

use anyhow::Context as _;
use borer_engine::program::checked_metadata;
use futures::FutureExt as _;
use futures::future::Shared;
use gpui::{App, BorrowAppContext as _, Global, SharedString, Task};
use settings::{
    ParseStatus, Settings as _, SettingsContent, SettingsFile, SettingsStore, ThemeAppearanceMode,
};
use theme::{ActiveTheme as _, Appearance, ThemeRegistry};
use theme_settings::ThemeSettings;

use crate::actions::{FollowSystemTheme, ToggleTheme};
use crate::binary::SettingsNotice;

/// The app's settings over Zed's defaults: AI off, borer's theme, fonts and density.
const APP_SETTINGS: &str = include_str!("../settings.json");

/// borer's theme family, `borer dark` and `borer light`, in Zed's theme format.
pub const BORER_THEME: &[u8] = include_bytes!("../themes/borer.json");

/// Most bytes a person's settings file may hold before the app refuses to read it.
const MAX_SETTINGS_BYTES: u64 = 1 << 20;

/// What a theme action makes of the theme mode the person's settings file holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ThemeChange {
    /// Dark becomes light and light dark; following the system becomes the other of what
    /// is shown.
    Flip,
    /// Follow the system's appearance.
    FollowSystem,
}

/// Loads borer's theme, applies the app's settings and the person's settings file, starts
/// reading and watching the person's themes folder ([`crate::user_themes`]), and registers
/// the theme actions.
///
/// A person's file that is missing is created empty, so it adds nothing and later writes
/// start from nothing rather than from Zed's template. One that does not read or parse
/// leaves the app's settings in force and says why on every status line.
///
/// # Arguments
///
/// * `cx` - Application context, Zed's settings store, themes and file system already set.
///
/// # Errors
///
/// Returns an error when borer's theme or the app's settings do not load.
pub fn apply(cx: &mut App) -> anyhow::Result<()> {
    theme_settings::load_user_theme(&ThemeRegistry::global(cx), BORER_THEME)
        .context("loading the borer theme")?;
    cx.update_global(|store: &mut SettingsStore, cx| {
        store.set_global_settings(APP_SETTINGS, cx).result()
    })
    .context("loading the app's settings")?;
    let notice = match load_person_settings(cx) {
        Ok(()) => file_notice(cx),
        Err(err) => Some(format!("settings file not applied: {err:#}").into()),
    };
    cx.set_global(SettingsNotice(notice));
    crate::user_themes::load_and_watch(cx);
    cx.on_action(|_: &ToggleTheme, cx| change_theme(ThemeChange::Flip, cx));
    cx.on_action(|_: &FollowSystemTheme, cx| change_theme(ThemeChange::FollowSystem, cx));
    Ok(())
}

/// Applies the person's settings file as Zed's user layer, creating it empty when missing;
/// how its fields parsed is [`file_notice`]'s to say.
///
/// # Arguments
///
/// * `cx` - Application context.
///
/// # Errors
///
/// Returns an error when [`check_settings_path`] refuses the path, or the file cannot be
/// stated, read or created; a file whose text does not parse at all is left out, and
/// [`file_notice`] says so.
fn load_person_settings(cx: &mut App) -> anyhow::Result<()> {
    let fs = <dyn fs::Fs>::global(cx);
    let path = &crate::app_dirs::settings_file();
    check_settings_path(path)?;
    let block = cx.foreground_executor().clone();
    let meta = block
        .block_on(fs.metadata(path))
        .with_context(|| format!("stating {}", path.display()))?;
    let text = if meta.is_some() {
        block
            .block_on(fs.load(path))
            .with_context(|| format!("reading {}", path.display()))?
    } else {
        block
            .block_on(fs.atomic_write(path.clone(), String::new()))
            .with_context(|| format!("creating {}", path.display()))?;
        String::new()
    };
    cx.update_global(|store: &mut SettingsStore, cx| drop(store.set_user_settings(&text, cx)));
    Ok(())
}

/// Refuses a settings path that is there but is not a small regular file.
///
/// Following links, a directory, device, pipe or socket is refused, and so is a file over
/// [`MAX_SETTINGS_BYTES`], so nothing blocks on it or reads a huge file; a path where
/// nothing is passes.
///
/// # Arguments
///
/// * `path` - The settings file's path.
///
/// # Errors
///
/// Returns an error naming the path and why it is refused.
fn check_settings_path(path: &Path) -> anyhow::Result<()> {
    check_path(path, MAX_SETTINGS_BYTES)
}

/// Refuses a path on disk that, following links, is there but is not a regular file or
/// holds over `max` bytes; a path where nothing is passes.
///
/// # Arguments
///
/// * `path` - The file's path.
/// * `max` - Most bytes the file may hold.
///
/// # Errors
///
/// Returns an error naming the path and why it is refused.
pub(crate) fn check_path(path: &Path, max: u64) -> anyhow::Result<()> {
    let meta = checked_metadata(path).map_err(|why| anyhow::anyhow!("{why}"))?;
    let Some(meta) = meta else {
        return Ok(());
    };
    if !meta.file_type().is_file() {
        anyhow::bail!("{} is not a regular file", path.display());
    }
    if meta.len() > max {
        anyhow::bail!(
            "{} holds {} bytes, over the {max} the app reads",
            path.display(),
            meta.len()
        );
    }
    Ok(())
}

/// Returns what the person's settings file's last parse leaves to say: nothing when every
/// field applied, which fields did not when the rest did, and that none did when its text
/// does not parse.
///
/// # Arguments
///
/// * `cx` - Application context reading Zed's settings store.
fn file_notice(cx: &App) -> Option<SharedString> {
    let store = cx.global::<SettingsStore>();
    let ParseStatus::Failed { error } = store.error_for_file(SettingsFile::User)?.parse_status
    else {
        return None;
    };
    let how = if store.raw_user_settings().is_some() {
        "partly applied"
    } else {
        "not applied"
    };
    Some(format!("settings file {how}: {error}").into())
}

/// Writes `change` of the theme mode to the person's settings file through Zed's settings
/// store, which applies it, and puts any failure on the status line.
///
/// Each change reads the mode the file holds when its write runs, so quick changes in a
/// row each see the one before. A single theme the settings name, with no dark and light
/// pair, stays, and the status line says so.
///
/// # Arguments
///
/// * `change` - What to make of the stored mode.
/// * `cx` - Application context.
pub(crate) fn change_theme(change: ThemeChange, cx: &mut App) {
    let theme_settings::ThemeSelection::Dynamic { mode, light, dark } =
        ThemeSettings::get_global(cx).theme.clone()
    else {
        let why = "the settings name one theme, not a dark and light pair; nothing to switch";
        cx.set_global(SettingsNotice(Some(why.into())));
        return;
    };
    let other = match cx.theme().appearance {
        Appearance::Dark => ThemeAppearanceMode::Light,
        Appearance::Light => ThemeAppearanceMode::Dark,
    };
    let done = write_settings(
        move |content| {
            let stored = match &content.theme.theme {
                Some(settings::ThemeSelection::Dynamic { mode, .. }) => *mode,
                Some(settings::ThemeSelection::Static(_)) | None => mode,
            };
            let next = match (change, stored) {
                (ThemeChange::FollowSystem, _) => ThemeAppearanceMode::System,
                (ThemeChange::Flip, ThemeAppearanceMode::Light) => ThemeAppearanceMode::Dark,
                (ThemeChange::Flip, ThemeAppearanceMode::Dark) => ThemeAppearanceMode::Light,
                (ThemeChange::Flip, ThemeAppearanceMode::System) => other,
            };
            content.theme.theme = Some(settings::ThemeSelection::Dynamic {
                mode: next,
                light,
                dark,
            });
        },
        cx,
    );
    cx.spawn(async move |cx| {
        let done = done.await;
        cx.update(|cx| {
            let notice = match done {
                Ok(()) => file_notice(cx),
                Err(err) => Some(format!("theme not saved: {err}").into()),
            };
            cx.set_global(SettingsNotice(notice));
        });
    })
    .detach();
}

/// The person's settings writes, newest last: each waits for the one before, so it reads
/// the file that one wrote.
#[derive(Default)]
struct SettingsWrites(Option<Shared<Task<Result<(), SharedString>>>>);

impl Global for SettingsWrites {}

/// Writes `edit` to the person's settings file in the app's config directory and applies
/// the file's new text as Zed's user layer, after the writes started before it.
///
/// Zed's own writer writes the settings file of Zed's config directory, which the app does
/// not keep its settings in ([`crate::app_dirs`]), so the app writes its file itself with
/// the same edit Zed makes: the text the file holds, changed only where `edit` changes it,
/// written where a link at the file's path leads, as Zed's writer does, so the link stays.
///
/// # Arguments
///
/// * `edit` - The change to the settings file's content.
/// * `cx` - Application context.
///
/// # Returns
///
/// The write, which says why when the file is refused or does not read or write; once the
/// file is written, how its new text applied is [`file_notice`]'s to say.
fn write_settings(
    edit: impl FnOnce(&mut SettingsContent) + 'static,
    cx: &mut App,
) -> Shared<Task<Result<(), SharedString>>> {
    let fs = <dyn fs::Fs>::global(cx);
    let before = cx.default_global::<SettingsWrites>().0.take();
    let write = cx.spawn(async move |cx| {
        if let Some(before) = before {
            drop(before.await);
        }
        let path = crate::app_dirs::settings_file();
        let shown = path.display();
        let written = async {
            check_settings_path(&path)?;
            let there = fs.metadata(&path).await;
            let (old, target) = match there.with_context(|| format!("stating {shown}"))? {
                Some(_) => (
                    (fs.load(&path).await).with_context(|| format!("reading {shown}"))?,
                    (fs.canonicalize(&path).await).with_context(|| format!("resolving {shown}"))?,
                ),
                None => (String::new(), path.clone()),
            };
            let new =
                cx.read_global(|store: &SettingsStore, _| store.new_text_for_update(old, edit))?;
            (fs.atomic_write(target.clone(), new.clone()).await)
                .with_context(|| format!("writing {}", target.display()))?;
            cx.update_global(|store: &mut SettingsStore, cx| {
                drop(store.set_user_settings(&new, cx));
            });
            anyhow::Ok(())
        };
        written.await.map_err(|err| format!("{err:#}").into())
    });
    let write = write.shared();
    cx.default_global::<SettingsWrites>().0 = Some(write.clone());
    write
}

/// Writes `edit` to the person's settings file with [`write_settings`], and puts a failure
/// on the status line as `what` not saved.
///
/// # Arguments
///
/// * `what` - What the edit saves, to name in a failure.
/// * `edit` - The change to the settings file's content.
/// * `cx` - Application context.
pub(crate) fn save_settings(
    what: &'static str,
    edit: impl FnOnce(&mut SettingsContent) + 'static,
    cx: &mut App,
) {
    let done = write_settings(edit, cx);
    cx.spawn(async move |cx| {
        let done = done.await;
        cx.update(|cx| {
            let notice = match done {
                Ok(()) => file_notice(cx),
                Err(err) => Some(format!("{what} not saved: {err}").into()),
            };
            cx.set_global(SettingsNotice(notice));
        });
    })
    .detach();
}

/// Returns `current` with `name` chosen as Zed's theme selector chooses it.
///
/// The light or dark slot is picked by `appearance`, and the mode is kept unless keeping
/// it would not show `name` under the `system` appearance; a single named theme is
/// replaced.
///
/// # Arguments
///
/// * `current` - The theme selection in force, as Zed's theme settings hold it.
/// * `name` - The chosen theme's name.
/// * `appearance` - The chosen theme's appearance.
/// * `system` - The system's appearance.
///
/// # Returns
///
/// The selection as a settings file holds it.
#[must_use]
pub fn choose_theme(
    current: &theme_settings::ThemeSelection,
    name: &str,
    appearance: Appearance,
    system: Appearance,
) -> settings::ThemeSelection {
    let current = match current.clone() {
        theme_settings::ThemeSelection::Static(theme) => settings::ThemeSelection::Static(theme),
        theme_settings::ThemeSelection::Dynamic { mode, light, dark } => {
            settings::ThemeSelection::Dynamic { mode, light, dark }
        }
    };
    let mut content = SettingsContent::default();
    content.theme.theme = Some(current.clone());
    theme_settings::set_theme(&mut content, name, appearance, system);
    content.theme.theme.unwrap_or(current)
}

#[cfg(test)]
mod tests {
    use super::{MAX_SETTINGS_BYTES, check_settings_path};

    /// A missing path and a small regular file pass; a directory and a file over the cap
    /// are refused with the path and the reason.
    ///
    /// # Panics
    ///
    /// Panics if a path is judged wrongly or the temporary files cannot be made.
    #[test]
    fn the_settings_path_must_be_a_small_regular_file() {
        let dir = std::env::temp_dir().join(format!("borer-app-settings-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let missing = dir.join("missing.json");
        assert!(check_settings_path(&missing).is_ok());
        let small = dir.join("small.json");
        std::fs::write(&small, "{}").unwrap();
        assert!(check_settings_path(&small).is_ok());
        let folder = dir.join("folder.json");
        std::fs::create_dir_all(&folder).unwrap();
        let err = check_settings_path(&folder).unwrap_err().to_string();
        assert!(err.contains("folder.json is not a regular file"), "{err}");
        let huge = dir.join("huge.json");
        let len = usize::try_from(MAX_SETTINGS_BYTES).unwrap() + 1;
        std::fs::write(&huge, vec![b' '; len]).unwrap();
        let err = check_settings_path(&huge).unwrap_err().to_string();
        assert!(
            err.contains("huge.json holds") && err.contains("over the"),
            "{err}"
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
