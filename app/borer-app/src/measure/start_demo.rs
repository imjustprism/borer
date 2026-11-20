//! The start page demo, `--start-demo`: the start page with a recent list, for screenshots.
//!
//! The demo opens a few binaries of the system one after another, so the window's recent
//! list holds them as any open does, closes the last, and announces the start page as
//! `START_STAGE start` ([`super::stage::stage`]); then `START_DONE`, and the app quits. Run
//! it over a fresh `--data-dir` to keep the person's own recent list out of the picture.

use std::path::PathBuf;

use gpui::{AsyncWindowContext, WeakEntity};

use super::stage::{poll, stage};
use super::{Harness, SYSTEM_NOTEPAD, say};
use crate::actions::CloseBinary;
use crate::start_item::StartItem;

/// The word this demo's stages are said with.
const START: &str = "START";

/// The system binaries the demo opens, the last one first in the recent list.
const SEEDS: [&str; 5] = [
    r"C:\Windows\System32\calc.exe",
    r"C:\Windows\System32\cmd.exe",
    r"C:\Windows\System32\where.exe",
    SYSTEM_NOTEPAD,
    r"C:\Windows\System32\xcopy.exe",
];

/// Opens each of [`SEEDS`], closes the binary and shows the start page.
///
/// # Errors
///
/// Off Windows, whose system binaries the seeds are; when a seed fails to load, naming it;
/// when the window is gone, a load never ends or stdout fails.
pub(super) async fn demo(
    this: &WeakEntity<Harness>,
    cx: &mut AsyncWindowContext,
) -> anyhow::Result<()> {
    anyhow::ensure!(
        cfg!(windows),
        "the start demo opens Windows system binaries as its recent list; run it on Windows"
    );
    for seed in SEEDS {
        let path = PathBuf::from(seed);
        this.update(cx, |h, cx| {
            h.binary.update(cx, |binary, cx| binary.open_path(path, cx));
        })?;
        poll("a load", cx, |cx| {
            this.read_with(cx, |h, cx| h.binary.read(cx).busy().is_none())
                .ok()
                .filter(|idle| *idle)
        })
        .await?;
        let failed = this.read_with(cx, |h, cx| {
            h.binary.read(cx).load_error().map(str::to_owned)
        })?;
        if let Some(err) = failed {
            anyhow::bail!("{seed} did not load: {err}");
        }
    }
    this.update_in(cx, |_, window, cx| {
        window.dispatch_action(Box::new(CloseBinary), cx);
    })?;
    poll("the start page", cx, |cx| {
        this.read_with(cx, |h, cx| {
            h.workspace
                .read(cx)
                .active_item_as::<StartItem>(cx)
                .is_some()
        })
        .ok()
        .filter(|shown| *shown)
    })
    .await?;
    stage(START, "start", cx).await?;
    say("START_DONE")
}
