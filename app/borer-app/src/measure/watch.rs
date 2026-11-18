//! The ack and settle detectors of the actions phase.
//!
//! Once a frame, the phase reads what the window shows ([`seen`]): a cheap [`Stamp`] of what
//! a person sees change, nothing they do not (no count of running requests), and whether the app is quiet, no [`Jobs`] request running and every
//! open view on the binary's state. A [`Watch`] started at an action's dispatch takes those
//! reads and names the frame of the first change (ack) and the frame after which the app is
//! quiet and the stamp holds for one more frame (settle).

use std::sync::Arc;
use std::time::Instant;

use gpui::{App, Entity, EntityId};
use picker::{Picker, PickerDelegate as _};
use workspace::Workspace;

use crate::binary::Binary;
use crate::decompile_item::DecompileItem;
use crate::functions_panel::FunctionsPanel;
use crate::goto::GoToDelegate;
use crate::places::view_of;
use crate::rows_panel::Rows as _;
use crate::worker::{Jobs, Referent};
use crate::xrefs::XrefsPanel;

/// What a person sees change in the window, cheap enough to read every frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Stamp {
    /// The active center item and the state it shows ([`crate::binary::Revision`]).
    active: Option<(EntityId, Option<u64>)>,
    /// The top line of the active code tab.
    top: Option<usize>,
    /// The functions panel's highlighted row and its filter's text.
    panel: Option<(usize, String)>,
    /// The go-to picker's query and its line count, while it is open.
    picker: Option<(String, usize)>,
    /// The xrefs panel's referent and the rows it shows, by identity: the rows change when
    /// an answer lands, not when its request starts.
    xrefs: Option<(Option<Referent>, Option<usize>)>,
    /// The status line.
    status: String,
}

/// One frame's read of the window.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Seen {
    /// What the frame shows.
    pub(super) stamp: Stamp,
    /// Whether no request runs and every open view shows the binary's state.
    pub(super) quiet: bool,
}

/// Reads what the window of `workspace` and `binary` shows now.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary.
/// * `cx` - Application context reading them.
pub(super) fn seen(workspace: &Entity<Workspace>, binary: &Entity<Binary>, cx: &App) -> Seen {
    let workspace = workspace.read(cx);
    let active = workspace.active_item(cx).map(|item| {
        let view = view_of(item.as_ref(), cx);
        (item.item_id(), view.and_then(|view| view.revision()))
    });
    let top = workspace
        .active_item_as::<DecompileItem>(cx)
        .map(|tab| tab.read(cx).top_line());
    let panel = workspace.panel::<FunctionsPanel>(cx).map(|panel| {
        let panel = panel.read(cx);
        (panel.selected(), panel.filter_text(cx))
    });
    let picker = workspace
        .active_modal::<Picker<GoToDelegate>>(cx)
        .map(|picker| {
            let picker = picker.read(cx);
            (picker.query(cx), picker.delegate.match_count())
        });
    let xrefs = workspace.panel::<XrefsPanel>(cx).map(|panel| {
        let panel = panel.read(cx);
        (
            *panel.target(),
            panel.rows().map(|rows| Arc::as_ptr(rows).addr()),
        )
    });
    let jobs = Jobs::running(cx).len();
    let now = binary.read(cx).loaded().map(|loaded| loaded.fingerprint);
    let current = workspace.panes().iter().all(|pane| {
        pane.read(cx)
            .items()
            .all(|item| view_of(item.as_ref(), cx).is_none_or(|view| view.revision() == now))
    });
    Seen {
        stamp: Stamp {
            active,
            top,
            panel,
            picker,
            xrefs,
            status: binary.read(cx).status().to_owned(),
        },
        quiet: jobs == 0 && current,
    }
}

/// The frames one action's change and its settling land on, from the stamp before it.
#[derive(Debug)]
pub(super) struct Watch {
    /// What the window showed before the action.
    before: Stamp,
    /// Start of the first frame showing a change.
    ack: Option<Instant>,
    /// Start of the latest quiet frame and what it showed, while the frames since are quiet.
    quiet: Option<(Instant, Stamp)>,
    /// Start of the frame after which the app is quiet and the stamp held one more frame.
    settle: Option<Instant>,
}

impl Watch {
    /// Starts watching from what the window showed before the action.
    ///
    /// # Arguments
    ///
    /// * `before` - The stamp read before the dispatch.
    pub(super) const fn new(before: Stamp) -> Self {
        Self {
            before,
            ack: None,
            quiet: None,
            settle: None,
        }
    }

    /// Takes the read of the frame starting at `at`.
    ///
    /// # Arguments
    ///
    /// * `at` - When the frame started, before it drew.
    /// * `seen` - What it shows.
    ///
    /// # Returns
    ///
    /// Whether the action has settled.
    pub(super) fn frame(&mut self, at: Instant, seen: Seen) -> bool {
        if self.ack.is_none() && seen.stamp != self.before {
            self.ack = Some(at);
        }
        if self.settle.is_some() {
            return true;
        }
        match self.quiet.take() {
            Some((since, stamp)) if seen.quiet && stamp == seen.stamp => {
                self.settle = Some(since);
            }
            _ => self.quiet = seen.quiet.then_some((at, seen.stamp)),
        }
        self.settle.is_some()
    }

    /// Returns the start of the first frame showing a change, `None` before one did.
    pub(super) const fn ack(&self) -> Option<Instant> {
        self.ack
    }

    /// Returns the start of the frame the action settled on, `None` before it did.
    pub(super) const fn settle(&self) -> Option<Instant> {
        self.settle
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    use borer_engine::analysis::Overlay;
    use gpui::{TestAppContext, VisualTestContext};

    use super::{Seen, Stamp, Watch, seen};
    use crate::actions::CycleSort;
    use crate::app_view::AppWindow;
    use crate::app_view::tests::{CALLEE, CALLER, init, load_sample, open, open_place, sample};
    use crate::binary::BinaryEvent;
    use crate::decompile_item::TabMode;
    use crate::measure::now_instant;
    use crate::places::Place;
    use crate::worker::{LoadedBinary, spawn_engine};

    /// Settles the work in flight and draws a frame.
    fn draw(cx: &mut VisualTestContext) {
        cx.run_until_parked();
        cx.update(|window, cx| window.draw(cx).clear(cx));
    }

    /// Reads what the window of `app` shows.
    fn look(app: &AppWindow, cx: &mut VisualTestContext) -> Seen {
        cx.update(|_, cx| seen(&app.workspace, &app.binary, cx))
    }

    /// Opens a window over the sample with its caller's decompile tab built and drawn, and
    /// returns the window, its context and the sample.
    fn with_caller(
        cx: &mut TestAppContext,
    ) -> (AppWindow, &mut VisualTestContext, Arc<LoadedBinary>) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let loaded = sample();
        load_sample(&app, cx);
        let place = Place::decompile(CALLER);
        open_place(&app.workspace, &loaded, place, TabMode::Permanent, cx);
        draw(cx);
        (app, cx, loaded)
    }

    /// Returns `t0` plus `ms` milliseconds.
    fn at(t0: Instant, ms: u64) -> Instant {
        t0 + Duration::from_millis(ms)
    }

    /// Settle waits until no request runs and every open view shows the binary's state,
    /// each alone holding it back, and fires on the frame after both clear, naming the
    /// first quiet frame.
    #[gpui::test]
    fn settle_waits_for_every_job_and_every_view(cx: &mut TestAppContext) {
        let (app, cx, loaded) = with_caller(cx);
        let t0 = now_instant();
        let mut watch = Watch::new(look(&app, cx).stamp);
        let renamed = loaded.with_overlay(Overlay {
            names: [(CALLEE, "renamed".to_owned())].into_iter().collect(),
            ..Overlay::default()
        });
        assert_ne!(renamed.fingerprint, loaded.fingerprint);
        let slow = cx.update(|_, cx| spawn_engine("Slow", cx, || ()));
        app.binary
            .update(cx, |binary, cx| binary.show_loaded(renamed.clone(), cx));
        draw(cx);
        for ms in 1..=2 {
            assert!(!watch.frame(at(t0, ms), look(&app, cx)), "a job and a view");
        }
        drop(slow);
        draw(cx);
        for ms in 3..=4 {
            assert!(!watch.frame(at(t0, ms), look(&app, cx)), "a view");
        }
        let slow = cx.update(|_, cx| spawn_engine("Slow", cx, || ()));
        app.binary
            .update(cx, |_, cx| cx.emit(BinaryEvent::Revised(renamed.clone())));
        draw(cx);
        for ms in 5..=6 {
            assert!(!watch.frame(at(t0, ms), look(&app, cx)), "a job");
        }
        drop(slow);
        draw(cx);
        assert!(!watch.frame(at(t0, 7), look(&app, cx)));
        assert!(watch.frame(at(t0, 8), look(&app, cx)));
        assert_eq!(watch.settle(), Some(at(t0, 7)));
    }

    /// An action that changes only the status line fires ack on the first frame read after
    /// it, and no frame read before it does.
    #[gpui::test]
    fn ack_fires_on_the_first_changed_frame(cx: &mut TestAppContext) {
        let (app, cx, _) = with_caller(cx);
        let t0 = now_instant();
        let before = look(&app, cx).stamp;
        let mut watch = Watch::new(before.clone());
        watch.frame(at(t0, 1), look(&app, cx));
        assert_eq!(watch.ack(), None);
        cx.update(|window, cx| window.dispatch_action(Box::new(CycleSort), cx));
        draw(cx);
        let after = look(&app, cx);
        assert_ne!(after.stamp.status, before.status);
        let others = Stamp {
            status: before.status.clone(),
            ..after.stamp.clone()
        };
        assert_eq!(others, before, "more than the status line changed");
        watch.frame(at(t0, 2), after);
        assert_eq!(watch.ack(), Some(at(t0, 2)));
    }
}
