//! The drop phase.
//!
//! A folder is dropped on the middle of the window through gpui's own file drop events,
//! once on the start tab and once on a decompile tab, each drop checked to have reached
//! the tab's handler, then the project's folders are counted; there must be none.

use std::path::{Path, PathBuf};
use std::time::Duration;

use gpui::{AsyncApp, ExternalPaths, FileDropEvent, PlatformInput, WeakEntity, point};

use super::{Harness, say};
use crate::app_view::REFUSED_FOLDER;
use crate::worker::ui_engine_calls;

/// Time a drop is given to add a folder or start a program before it is checked.
const DROP_SETTLE: Duration = Duration::from_secs(3);

/// Time between a drag entering the window and its drop, so a frame lays out the hover
/// the drop is tested against, as between a system drag's last move and its release.
const DROP_HOVER: Duration = Duration::from_millis(200);

/// Interval at which the phase polls for the binary's first decompile tab.
const TAB_POLL: Duration = Duration::from_millis(50);

/// Polls for the first decompile tab before the phase gives up (30 s).
const TAB_POLLS: u32 = 600;

impl Harness {
    /// Drops `dir` on the start tab, opens `binary`, drops `dir` on its first decompile
    /// tab, then reports `DROP_DONE` and quits.
    ///
    /// # Arguments
    ///
    /// * `dir` - The folder to drop.
    /// * `binary` - The binary whose tab the second drop lands on.
    /// * `cx` - Harness context.
    pub(super) fn drop_folder(
        &mut self,
        dir: PathBuf,
        binary: PathBuf,
        cx: &mut gpui::Context<'_, Self>,
    ) {
        let exit = self.exit.clone();
        self.task = Some(cx.spawn(async move |this, cx| {
            if let Err(err) = drop_twice(&this, &dir, binary, cx).await {
                *exit.borrow_mut() = Some(err.context("drop phase"));
                cx.update(|cx| cx.quit());
            }
        }));
    }
}

/// Runs the two drops of the phase and prints its report.
///
/// # Arguments
///
/// * `this` - The harness.
/// * `dir` - The folder to drop.
/// * `binary` - The binary whose tab the second drop lands on.
/// * `cx` - Async application context.
///
/// # Errors
///
/// Returns an error when the window is gone, the binary shows no tab within 30 seconds,
/// or stdout fails.
async fn drop_twice(
    this: &WeakEntity<Harness>,
    dir: &Path,
    binary: PathBuf,
    cx: &mut AsyncApp,
) -> anyhow::Result<()> {
    let on_start = drop_and_check(this, dir, cx).await?;
    this.update(cx, |harness, cx| {
        harness
            .binary
            .update(cx, |loaded, cx| loaded.open_path(binary, cx));
    })?;
    let mut polls = 0;
    while !this.update(cx, |harness, cx| {
        harness
            .item(cx)
            .is_some_and(|item| item.read(cx).code().is_some())
    })? {
        polls += 1;
        anyhow::ensure!(polls < TAB_POLLS, "the binary showed no decompile tab");
        cx.background_executor().timer(TAB_POLL).await;
    }
    let on_tab = drop_and_check(this, dir, cx).await?;
    this.update(cx, |harness, cx| {
        let folders = harness
            .workspace
            .read(cx)
            .project()
            .read(cx)
            .worktrees(cx)
            .count();
        say(&format!(
            "DROP_DONE folders={folders} on_start={on_start} on_tab={on_tab} ui_engine_calls={}",
            ui_engine_calls()
        ))?;
        cx.quit();
        Ok(())
    })?
}

/// Drops `dir` on the middle of the window, waits, and returns whether a tab refused it.
///
/// # Arguments
///
/// * `this` - The harness.
/// * `dir` - The folder to drop.
/// * `cx` - Async application context.
///
/// # Errors
///
/// Returns an error when the window is gone.
async fn drop_and_check(
    this: &WeakEntity<Harness>,
    dir: &Path,
    cx: &mut AsyncApp,
) -> anyhow::Result<bool> {
    let dir = dir.to_path_buf();
    let position = this.update_in(cx, |harness, window, cx| {
        harness
            .binary
            .update(cx, |binary, cx| binary.set_status(String::new(), cx));
        let size = window.viewport_size();
        let position = point(size.width * 0.5, size.height * 0.5);
        window.defer(cx, move |window, cx| {
            let paths = ExternalPaths([dir].into_iter().collect());
            let entered = FileDropEvent::Entered { position, paths };
            window.dispatch_event(PlatformInput::FileDrop(entered), cx);
        });
        position
    })?;
    cx.background_executor().timer(DROP_HOVER).await;
    this.update_in(cx, |_, window, cx| {
        window.defer(cx, move |window, cx| {
            let submit = FileDropEvent::Submit { position };
            window.dispatch_event(PlatformInput::FileDrop(submit), cx);
        });
    })?;
    cx.background_executor().timer(DROP_SETTLE).await;
    this.update(cx, |harness, cx| {
        harness.binary.read(cx).status().ends_with(REFUSED_FOLDER)
    })
}
