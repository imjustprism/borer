//! The drop phase.
//!
//! A folder is dropped on the middle of the window through gpui's own file drop events,
//! then, after the drop had time to start anything, the project's folders are counted;
//! there must be none.

use std::path::PathBuf;
use std::time::Duration;

use gpui::{Context, ExternalPaths, FileDropEvent, PlatformInput, Window, point};

use super::{Harness, say};
use crate::worker::ui_engine_calls;

/// Time a drop is given to add a folder or start a program before the phase reports.
const DROP_SETTLE: Duration = Duration::from_secs(3);

impl Harness {
    /// Drops `dir` on the middle of the window, then reports `DROP_DONE` and quits.
    ///
    /// # Arguments
    ///
    /// * `dir` - The folder to drop.
    /// * `window` - Window receiving the drop.
    /// * `cx` - Harness context.
    pub(super) fn drop_folder(
        &mut self,
        dir: PathBuf,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let size = window.viewport_size();
        let position = point(size.width * 0.5, size.height * 0.5);
        window.defer(cx, move |window, cx| {
            let paths = ExternalPaths([dir].into_iter().collect());
            let entered = FileDropEvent::Entered { position, paths };
            window.dispatch_event(PlatformInput::FileDrop(entered), cx);
            let submit = FileDropEvent::Submit { position };
            window.dispatch_event(PlatformInput::FileDrop(submit), cx);
        });
        let settle = cx.background_executor().timer(DROP_SETTLE);
        let exit = self.exit.clone();
        self.task = Some(cx.spawn(async move |this, cx| {
            settle.await;
            let reported = this.update(cx, |harness, cx| {
                let folders = harness
                    .workspace
                    .read(cx)
                    .project()
                    .read(cx)
                    .worktrees(cx)
                    .count();
                let line = format!(
                    "DROP_DONE folders={folders} ui_engine_calls={}",
                    ui_engine_calls()
                );
                match say(&line) {
                    Ok(()) => cx.quit(),
                    Err(err) => harness.fail(err, cx),
                }
            });
            if let Err(err) = reported {
                *exit.borrow_mut() = Some(err.context("the measured window is gone"));
                cx.update(|cx| cx.quit());
            }
        }));
    }
}
