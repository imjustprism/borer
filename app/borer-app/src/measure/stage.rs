//! What the scripted demos share: saying a stage is on screen and holding it for its
//! capture, and waiting for what the next stage needs.

use std::time::Duration;

use gpui::{AsyncApp, AsyncWindowContext, Context, WeakEntity, Window};

use super::{Harness, say};

/// How long each stage stays on screen for its capture.
const HOLD: Duration = Duration::from_secs(4);

/// Interval at which a demo polls for what it waits on.
pub(super) const POLL: Duration = Duration::from_millis(100);

/// Most polls before a demo gives up on a wait (60 s).
const POLLS: u32 = 600;

/// Says `<demo>_STAGE <name>` and holds the stage on screen for [`HOLD`].
///
/// # Arguments
///
/// * `demo` - The demo's word (`CHAT`, `ANNOTATE`).
/// * `name` - The stage's name, which names its capture.
/// * `cx` - Async context.
///
/// # Errors
///
/// When stdout fails.
pub(super) async fn stage(demo: &str, name: &str, cx: &AsyncApp) -> anyhow::Result<()> {
    say(&format!("{demo}_STAGE {name}"))?;
    cx.background_executor().timer(HOLD).await;
    Ok(())
}

/// Polls `found` every [`POLL`] until it gives a value.
///
/// # Arguments
///
/// * `what` - What is waited on, for the error.
/// * `cx` - Async context.
/// * `found` - Gives the value once it is there.
///
/// # Errors
///
/// When `what` is still not there after [`POLLS`] polls.
pub(super) async fn poll<T>(
    what: &str,
    cx: &mut AsyncApp,
    mut found: impl FnMut(&mut AsyncApp) -> Option<T>,
) -> anyhow::Result<T> {
    for _ in 0..POLLS {
        if let Some(value) = found(cx) {
            return Ok(value);
        }
        cx.background_executor().timer(POLL).await;
    }
    anyhow::bail!("{what} never came")
}

impl Harness {
    /// Runs `demo` in the harness's window, keeps its error, named for `name`, for the
    /// exit status, and quits the app once it ends.
    ///
    /// # Arguments
    ///
    /// * `name` - What the demo is called in its error (`annotate demo`).
    /// * `demo` - The demo's steps.
    /// * `window` - The harness's window.
    /// * `cx` - Harness context.
    pub(super) fn run_demo(
        &mut self,
        name: &'static str,
        demo: impl AsyncFnOnce(&WeakEntity<Self>, &mut AsyncWindowContext) -> anyhow::Result<()>
        + 'static,
        window: &Window,
        cx: &mut Context<'_, Self>,
    ) {
        let exit = self.exit.clone();
        self.task = Some(cx.spawn_in(window, async move |this, cx| {
            if let Err(err) = demo(&this, cx).await {
                *exit.borrow_mut() = Some(err.context(name));
            }
            cx.update(|_, cx| cx.quit()).unwrap_or(());
        }));
    }
}
