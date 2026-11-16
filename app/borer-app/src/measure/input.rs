//! The input-latency phase: real `SendInput` keys and clicks, each marked from its
//! injection to the frame that presents its result.

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};

use borer_engine::cancel::Cancel;
use borer_engine::view::Ref;
use gpui::{App, Context, Window, px};

use super::{
    CALL_CLICKS, FILTER_KEYS, Harness, InjectTracker, MarkWait, PendingInputMark, nanos,
    now_instant, ns_to_ms, say, sorted_quantiles_ms,
};
use crate::code_view::{CodePalette, style_view_line};
use crate::decompile_item::{
    CODE_PAD_PX, CODE_ROW_HEIGHT_PX, DecompileItem, TabMode, open_function,
};
use crate::functions_panel::FunctionsPanel;
use crate::worker::{LoadedBinary, decompile_blocking, ui_engine_calls};

/// Action selected for a frame where a clickable call token is visible.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TargetDecision {
    /// Print `CALL_TARGET` so the controller injects the next click.
    Emit,
    /// Keep waiting for an already-announced click to complete.
    Wait,
    /// Abort cleanly after exhausting bounded re-announcements without click progress.
    Abort,
}

/// Tracks `CALL_TARGET` announcements, recovery re-announcements, and bounded click retries.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CallTargetTracker {
    /// Click count most recently announced on `CALL_TARGET`, if any.
    last_reported_clicks: Option<u64>,
    /// Timestamp when [`Self::last_reported_clicks`] was last announced.
    last_reported_at: Option<Instant>,
    /// Whether `navigate_back` recovery requires re-announcing a visible target at the same count.
    reannounce_after_back: bool,
    /// Consecutive re-announcements emitted without `clicks` advancing.
    retries_at_count: u8,
    /// Consecutive `navigate_back` recoveries without `clicks` advancing.
    stalled_backs: u8,
}

impl CallTargetTracker {
    /// Creates an idle [`CallTargetTracker`] prior to the first `CALL_TARGET` emission.
    ///
    /// # Returns
    ///
    /// Initialized [`CallTargetTracker`].
    const fn new() -> Self {
        Self {
            last_reported_clicks: None,
            last_reported_at: None,
            reannounce_after_back: false,
            retries_at_count: 0,
            stalled_backs: 0,
        }
    }

    /// Decides whether to emit `CALL_TARGET`, wait, or abort when a call token is visible.
    ///
    /// # Arguments
    ///
    /// * `clicks` - Clicks that opened a function so far.
    /// * `now` - Current [`Instant`].
    ///
    /// # Returns
    ///
    /// [`TargetDecision`] governing the current frame.
    fn decide_visible(&mut self, clicks: u64, now: Instant) -> TargetDecision {
        if self.last_reported_clicks != Some(clicks) {
            self.last_reported_clicks = Some(clicks);
            self.last_reported_at = Some(now);
            self.reannounce_after_back = false;
            self.retries_at_count = 0;
            self.stalled_backs = 0;
            return TargetDecision::Emit;
        }
        let timed_out = self
            .last_reported_at
            .is_some_and(|t| now.saturating_duration_since(t) >= Duration::from_secs(1));
        if !self.reannounce_after_back && !timed_out {
            return TargetDecision::Wait;
        }
        if self.retries_at_count >= 8 {
            return TargetDecision::Abort;
        }
        self.retries_at_count = self.retries_at_count.saturating_add(1);
        self.reannounce_after_back = false;
        self.last_reported_at = Some(now);
        TargetDecision::Emit
    }

    /// Records a `navigate_back` recovery step when a callee view lacks visible call tokens.
    ///
    /// # Arguments
    ///
    /// * `can_go_back` - Whether the pane's nav history holds an earlier place to go back to.
    ///
    /// # Returns
    ///
    /// `true` when recovery may call `navigate_back`, `false` when recovery attempts are exhausted.
    fn note_back(&mut self, can_go_back: bool) -> bool {
        if !can_go_back || self.stalled_backs >= 8 {
            return false;
        }
        self.stalled_backs = self.stalled_backs.saturating_add(1);
        self.reannounce_after_back = true;
        true
    }
}

/// Unadjusted latency durations captured when a [`PendingInputMark`] is presented.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RetiredInputSample {
    /// Monotonic controller event identifier (`0` when unnumbered).
    id: u64,
    /// Elapsed nanoseconds from `MARK` to GPUI event arrival (`arrived_at - injected_at`).
    raw_queue_ns: u64,
    /// Elapsed nanoseconds from `MARK` to frame presentation (`present_end - injected_at`).
    raw_e2e_ns: u64,
    /// Elapsed nanoseconds from event arrival until the background work it started was
    /// settled (`ready_at - arrived_at`); zero for an event that started none.
    work_ns: u64,
}

/// Whether the input phase goes on after this frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InputStep {
    /// Poll again on the next frame.
    Continue,
    /// Every key and click is presented: report.
    Done,
}

/// State of the input phase, carried from frame to frame.
pub(super) struct InputRun {
    /// Measurement generation ticket owning this input benchmark.
    ticket: u64,
    /// Cooperative [`Cancel`] flag owning this input benchmark.
    cancel: Cancel,
    /// Target [`gpui::WindowId`] filtering profiler [`gpui::profiler::FrameEvent`] entries.
    window_id: gpui::WindowId,
    /// Whether GPUI profiler tracing was already enabled before this run started.
    was_trace_enabled: bool,
    /// Cursor draining newly recorded [`gpui::profiler::FrameEvent`] entries.
    collector: gpui::profiler::FrameTimingCollector,
    /// Start timestamp of the latest `Window::draw` awaiting presentation.
    pending_draw_start: Option<Instant>,
    /// Baseline snapshot captured before input injection started.
    before: gpui::profiler::InputLatencySnapshot,
    /// Presented input samples awaiting final `SENT <id> <delta_ns>` adjustment.
    retired: Vec<RetiredInputSample>,
    /// `true` once `INPUT_FILTER_READY` has been printed.
    announced: bool,
    /// `CALL_TARGET` emission and recovery state machine.
    targets: CallTargetTracker,
    /// Consecutive frames where the opened callee lacked a visible call token.
    empty_frames: u8,
    /// Post-completion frames awaited so the 100th click's presentation is captured.
    settle_frames: u8,
}

impl Drop for InputRun {
    fn drop(&mut self) {
        if !self.was_trace_enabled {
            gpui::profiler::set_trace_enabled(false);
        }
    }
}

impl Harness {
    /// Opens `entry` in the preview tab with the filter focused, then polls the input phase;
    /// the functions panel already lists `loaded`.
    ///
    /// # Arguments
    ///
    /// * `ticket` - Generation of the phase.
    /// * `cancel` - Cancel flag of the phase.
    /// * `loaded` - Notepad, analyzed.
    /// * `entry` - A function with a call token near its top.
    /// * `window` - Window receiving real OS keyboard and mouse events.
    /// * `cx` - Harness context.
    pub(super) fn start_input(
        &mut self,
        ticket: u64,
        cancel: Cancel,
        loaded: Arc<LoadedBinary>,
        entry: u64,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.workspace.update(cx, |workspace, cx| {
            open_function(
                workspace,
                loaded,
                entry,
                TabMode::Preview,
                false,
                window,
                cx,
            );
            workspace.focus_panel::<FunctionsPanel>(window, cx);
        });
        self.keys = 0;
        self.clicks = 0;
        self.before = None;
        self.marks.clear();
        let run = InputRun {
            ticket,
            cancel,
            window_id: window.window_handle().window_id(),
            was_trace_enabled: gpui::profiler::set_trace_enabled(true),
            collector: gpui::profiler::FrameTimingCollector::new(),
            pending_draw_start: None,
            before: window.input_latency_snapshot(),
            retired: Vec::with_capacity(512),
            announced: false,
            targets: CallTargetTracker::new(),
            empty_frames: 0,
            settle_frames: 0,
        };
        cx.on_next_frame(window, move |this, window, cx| {
            this.input_step(run, window, cx);
        });
    }

    /// Retires presented marks and takes the phase's next step.
    ///
    /// # Arguments
    ///
    /// * `run` - The phase's state.
    /// * `window` - Window scheduling the next-frame callback.
    /// * `cx` - Harness context.
    pub(super) fn input_step(
        &mut self,
        mut run: InputRun,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        if !self.epoch.is_current(run.ticket, &run.cancel) {
            return;
        }
        let events = run.collector.collect_unseen();
        retire_presented_marks(
            &mut self.marks,
            &mut run.pending_draw_start,
            run.window_id,
            &events,
            &mut run.retired,
        );
        match self.input_decide(&mut run, window, cx) {
            Ok(InputStep::Continue) => {
                cx.on_next_frame(window, move |this, window, cx| {
                    this.input_step(run, window, cx);
                });
            }
            Ok(InputStep::Done) => match self.input_report(&run, window).and_then(|l| say(&l)) {
                Ok(()) => cx.quit(),
                Err(err) => self.fail(err, cx),
            },
            Err(err) => self.fail(err, cx),
        }
    }

    /// Returns whether the work `wait` names is on screen, superseded, or never started.
    ///
    /// # Arguments
    ///
    /// * `wait` - The work a mark waits on.
    /// * `cx` - Application context reading the panel and the active tab.
    pub(super) fn settled(&self, wait: MarkWait, cx: &App) -> bool {
        match wait {
            MarkWait::Immediate => true,
            MarkWait::Filter(seq) => self
                .panel(cx)
                .is_none_or(|panel| panel.read(cx).filter_settled(seq)),
            MarkWait::Decompile(id, ticket) => self.item(cx).is_none_or(|item| {
                item.entity_id() != id || item.read(cx).decompile_settled(ticket)
            }),
        }
    }

    /// Marks ready every pending mark whose background work the app has settled.
    ///
    /// Runs whenever the panel or the active tab notifies, so the readiness time is when
    /// the app changed, before any frame that draws the change; a frame polled before it
    /// can be drawn without the poll, so settling there would retire marks late.
    ///
    /// # Arguments
    ///
    /// * `cx` - Harness context reading the app.
    pub(super) fn settle_marks(&mut self, cx: &App) {
        let now = now_instant();
        let waits: Vec<_> = self
            .marks
            .iter()
            .map(|m| m.ready_at.is_none() && self.settled(m.wait, cx))
            .collect();
        for (mark, settled) in self.marks.iter_mut().zip(waits) {
            if settled {
                mark.ready_at = Some(now);
                mark.wait = MarkWait::Immediate;
            }
        }
    }

    /// Announces the filter, waits for the keys, then announces call targets until the
    /// clicks are done.
    ///
    /// # Arguments
    ///
    /// * `run` - The phase's state.
    /// * `window` - Window shaping the call target's line.
    /// * `cx` - Harness context.
    ///
    /// # Errors
    ///
    /// Returns an error when stdout fails or the call targets run out.
    fn input_decide(
        &mut self,
        run: &mut InputRun,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) -> anyhow::Result<InputStep> {
        let (shown, decompiling, can_back) = {
            let item_entity = self.item(cx);
            let item = item_entity.as_ref().map(|item| item.read(cx));
            (
                item.is_some_and(|item| item.code().is_some()),
                item.is_some_and(DecompileItem::is_decompiling),
                self.workspace
                    .read(cx)
                    .active_pane()
                    .read(cx)
                    .can_navigate_backward(),
            )
        };
        if !shown {
            return Ok(InputStep::Continue);
        }
        if !run.announced {
            run.announced = true;
            say(&format!("INPUT_FILTER_READY pid={}", std::process::id()))?;
            return Ok(InputStep::Continue);
        }
        if self.keys < FILTER_KEYS {
            return Ok(InputStep::Continue);
        }
        if decompiling {
            run.empty_frames = 0;
            return Ok(InputStep::Continue);
        }
        let clicks = self.clicks;
        if clicks >= CALL_CLICKS {
            run.settle_frames = run.settle_frames.saturating_add(1);
            let settled =
                (self.marks.is_empty() && run.settle_frames >= 2) || run.settle_frames >= 10;
            return Ok(if settled {
                InputStep::Done
            } else {
                InputStep::Continue
            });
        }
        if let Some((x, y)) = self.call_target(window, cx) {
            run.empty_frames = 0;
            match run.targets.decide_visible(clicks, now_instant()) {
                TargetDecision::Emit => {
                    say(&format!("CALL_TARGET x={x:.2} y={y:.2} clicks={clicks}"))?;
                }
                TargetDecision::Wait => {}
                TargetDecision::Abort => anyhow::bail!(
                    "input latency benchmark stalled at click {clicks} after 8 retries"
                ),
            }
            return Ok(InputStep::Continue);
        }
        run.empty_frames = run.empty_frames.saturating_add(1);
        if run.empty_frames >= 3 {
            run.empty_frames = 0;
            if !run.targets.note_back(can_back) {
                anyhow::bail!(
                    "input latency benchmark lost visible call target after {clicks} clicks"
                );
            }
            self.before = None;
            window.dispatch_action(Box::new(workspace::pane::GoBack), cx);
        }
        Ok(InputStep::Continue)
    }

    /// Returns the window position of a visible call token, preferring a call to another
    /// function, found from the app's shown lines and its code list's laid-out bounds.
    ///
    /// # Arguments
    ///
    /// * `window` - Window shaping the token's line exactly as the code pane does.
    /// * `cx` - Application context reading the app and the theme.
    ///
    /// # Returns
    ///
    /// Logical `(x, y)` window coordinates, or `None` when no call token is visible.
    fn call_target(&self, window: &Window, cx: &App) -> Option<(f32, f32)> {
        let item_entity = self.item(cx)?;
        let item = item_entity.read(cx);
        let code = item.code()?;
        let current = item.entry();
        let (bounds, offset) = {
            let state = item.code_scroll().0.borrow();
            (state.base_handle.bounds(), state.base_handle.offset())
        };
        let row = px(CODE_ROW_HEIGHT_PX);
        let mut top = bounds.top() + offset.y;
        let mut found = None;
        for ix in 0..code.len() {
            let center = top + row * 0.5;
            top += row;
            if center < bounds.top() {
                continue;
            }
            if center > bounds.bottom() {
                break;
            }
            let Some((view, line_ix)) = code.get(ix) else {
                break;
            };
            let call = view.tokens(line_ix).find_map(|(span, _, link)| match link {
                Some(Ref::Function(t)) => Some((span.start, Some(*t) != current)),
                _ => None,
            });
            match call {
                Some((start, true)) => {
                    found = Some((view, line_ix, start, center));
                    break;
                }
                Some((start, false)) if found.is_none() => {
                    found = Some((view, line_ix, start, center));
                }
                Some(_) | None => {}
            }
        }
        let (view, line_ix, start, center) = found?;
        let settings = theme::theme_settings(cx);
        let (font, size) = (
            settings.buffer_font(cx).clone(),
            settings.buffer_font_size(cx),
        );
        let styled = style_view_line(view, line_ix, &font, &CodePalette::from_theme(cx));
        let shaped = window
            .text_system()
            .shape_line(styled.text, size, &styled.runs, None);
        let x = bounds.left() + offset.x + px(CODE_PAD_PX) + shaped.x_for_index(start) + px(3.0);
        Some((f32::from(x), f32::from(center)))
    }

    /// Returns the `MEASURE_INPUT` quantile summary line once the clicks complete.
    ///
    /// # Arguments
    ///
    /// * `run` - The finished phase's state.
    /// * `window` - Window providing the post-run input-latency snapshot.
    ///
    /// # Errors
    ///
    /// Returns an error when the latency histograms cannot be subtracted.
    fn input_report(&self, run: &InputRun, window: &Window) -> anyhow::Result<String> {
        let after = window.input_latency_snapshot();
        let mut lat = after.latency_histogram.clone();
        lat.subtract(&run.before.latency_histogram)?;
        let (mut queue_samples_ns, mut e2e_samples_ns) =
            apply_sent_offsets(&run.retired, self.inject.as_deref());
        let (ep50, ep95, ep99, emax, ecount) = if e2e_samples_ns.is_empty() {
            (
                ns_to_ms(lat.value_at_quantile(0.50)),
                ns_to_ms(lat.value_at_quantile(0.95)),
                ns_to_ms(lat.value_at_quantile(0.99)),
                ns_to_ms(lat.max()),
                lat.len(),
            )
        } else {
            sorted_quantiles_ms(&mut e2e_samples_ns)
        };
        let (qp50, qp95, qp99, qmax, qcount) = sorted_quantiles_ms(&mut queue_samples_ns);
        let mut work_samples_ns: Vec<u64> = run
            .retired
            .iter()
            .map(|s| s.work_ns)
            .filter(|&ns| ns > 0)
            .collect();
        let (wp50, wp95, wp99, wmax, wcount) = sorted_quantiles_ms(&mut work_samples_ns);
        Ok(format!(
            "MEASURE_INPUT samples={ecount} p50_ms={ep50:.3} p95_ms={ep95:.3} p99_ms={ep99:.3} max_ms={emax:.3} \
queue_samples={qcount} queue_p50_ms={qp50:.3} queue_p95_ms={qp95:.3} queue_p99_ms={qp99:.3} queue_max_ms={qmax:.3} work_samples={wcount} work_p50_ms={wp50:.3} work_p95_ms={wp95:.3} work_p99_ms={wp99:.3} work_max_ms={wmax:.3} \
gpui_samples={} gpui_p50_ms={:.3} gpui_p95_ms={:.3} gpui_p99_ms={:.3} gpui_max_ms={:.3} \
filter_keys={} call_clicks={} mid_draw_dropped={} ui_engine_calls={}",
            lat.len(),
            ns_to_ms(lat.value_at_quantile(0.50)),
            ns_to_ms(lat.value_at_quantile(0.95)),
            ns_to_ms(lat.value_at_quantile(0.99)),
            ns_to_ms(lat.max()),
            self.keys,
            self.clicks,
            after
                .mid_draw_events_dropped
                .saturating_sub(run.before.mid_draw_events_dropped),
            ui_engine_calls(),
        ))
    }
}

/// Retires every ready [`PendingInputMark`] included in newly presented frames for `window_id`.
///
/// A mark retires only when [`PendingInputMark::ready_at`] is `Some(ready)` with
/// `ready <= draw_start`, so loading frames never retire marks awaiting background filter or
/// decompile completion.
///
/// # Arguments
///
/// * `pending_marks` - Queue of unpresented [`PendingInputMark`] entries.
/// * `pending_draw_start` - Latest `draw_start` observed for `window_id` prior to `Present`.
/// * `window_id` - Window whose draw/present events are being retired.
/// * `events` - Newly drained [`gpui::profiler::FrameEvent`] slice.
/// * `retired_out` - Destination buffer receiving unadjusted [`RetiredInputSample`] records.
fn retire_presented_marks(
    pending_marks: &mut VecDeque<PendingInputMark>,
    pending_draw_start: &mut Option<Instant>,
    window_id: gpui::WindowId,
    events: &[gpui::profiler::FrameEvent],
    retired_out: &mut Vec<RetiredInputSample>,
) {
    for event in events {
        match event {
            gpui::profiler::FrameEvent::Draw(draw) if draw.window_id == window_id => {
                *pending_draw_start = Some(draw.draw_start);
            }
            gpui::profiler::FrameEvent::Present(present) if present.window_id == window_id => {
                let cutoff = pending_draw_start.take().unwrap_or(present.present_start);
                pending_marks.retain(|mark| {
                    let Some(ready) = mark.ready_at else {
                        return true;
                    };
                    if ready > cutoff {
                        return true;
                    }
                    retired_out.push(RetiredInputSample {
                        id: mark.id,
                        raw_queue_ns: nanos(
                            mark.arrived_at.saturating_duration_since(mark.injected_at),
                        ),
                        work_ns: nanos(ready.saturating_duration_since(mark.arrived_at)),
                        raw_e2e_ns: nanos(
                            present
                                .present_end
                                .saturating_duration_since(mark.injected_at),
                        ),
                    });
                    false
                });
            }
            gpui::profiler::FrameEvent::Draw(_) | gpui::profiler::FrameEvent::Present(_) => {}
        }
    }
}

/// Adjusts retired input samples by subtracting each event's post-`MARK_OK` `SendInput` offset.
///
/// # Arguments
///
/// * `samples` - Retired `(id, raw_queue_ns, raw_e2e_ns)` records in presentation order.
/// * `tracker` - Optional [`InjectTracker`] holding `SENT <id> <delta_ns>` controller offsets.
///
/// # Returns
///
/// `(queue_samples_ns, e2e_samples_ns)` anchored to `SendInput` and clamped at `arrived_at`.
fn apply_sent_offsets(
    samples: &[RetiredInputSample],
    tracker: Option<&InjectTracker>,
) -> (Vec<u64>, Vec<u64>) {
    let mut queue_out = Vec::with_capacity(samples.len());
    let mut e2e_out = Vec::with_capacity(samples.len());
    for sample in samples {
        let delta_ns = tracker
            .and_then(|t| t.take_sent_offset(sample.id))
            .unwrap_or(0)
            .min(sample.raw_queue_ns);
        queue_out.push(sample.raw_queue_ns.saturating_sub(delta_ns));
        e2e_out.push(sample.raw_e2e_ns.saturating_sub(delta_ns));
    }
    (queue_out, e2e_out)
}

/// Selects a function entry in `loaded` whose top lines contain a clickable `Ref::Function` call.
///
/// Must be called on the background engine executor before the input phase starts.
///
/// # Arguments
///
/// * `loaded` - Analyzed binary state.
///
/// # Returns
///
/// Entry address of a function with a visible `Ref::Function` token near line 0, or `None` when
/// no function in `loaded` exposes one.
pub(super) fn pick_function_with_callees(loaded: &LoadedBinary) -> Option<u64> {
    loaded.analysis.functions.iter().find_map(|f| {
        if f.thunk.is_some() || f.callees.is_empty() || f.blocks.len() < 2 {
            return None;
        }
        let v = decompile_blocking(loaded, f.entry)?;
        let top = v.lines().min(15);
        (0..top)
            .any(|line_ix| {
                v.tokens(line_ix)
                    .any(|(_, _, r)| matches!(r, Some(Ref::Function(t)) if *t != f.entry))
            })
            .then_some(f.entry)
    })
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;
    use std::time::Duration;

    use super::{
        CallTargetTracker, InjectTracker, MarkWait, PendingInputMark, TargetDecision,
        apply_sent_offsets, now_instant, retire_presented_marks,
    };

    /// Event-associated retirement preserves exact per-event totals across multi-frame batches.
    ///
    /// # Panics
    ///
    /// Panics if `(queue=1ms, gpui=100ms)` and `(queue=100ms, gpui=1ms)` are mispaired as `2ms`
    /// and `200ms` instead of `101ms` each, or if a post-draw arrival is retired early.
    #[test]
    fn event_associated_retirement_preserves_exact_per_event_totals() {
        let win = gpui::WindowId::from(7);
        let t0 = now_instant();
        let ms = |n: u64| t0 + Duration::from_millis(n);
        let mut pending = VecDeque::from([
            PendingInputMark {
                id: 1,
                injected_at: ms(0),
                arrived_at: ms(1),
                ready_at: Some(ms(1)),
                wait: MarkWait::Immediate,
            },
            PendingInputMark {
                id: 2,
                injected_at: ms(200),
                arrived_at: ms(300),
                ready_at: Some(ms(300)),
                wait: MarkWait::Immediate,
            },
            PendingInputMark {
                id: 3,
                injected_at: ms(301),
                arrived_at: ms(302),
                ready_at: Some(ms(302)),
                wait: MarkWait::Immediate,
            },
        ]);
        let events = [
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(1)),
                invalidations: 1,
                draw_start: ms(2),
                draw_end: ms(50),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(50),
                present_end: ms(101),
                animation_interval: None,
            }),
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(300)),
                invalidations: 1,
                draw_start: ms(300),
                draw_end: ms(301),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(301),
                present_end: ms(301),
                animation_interval: None,
            }),
        ];
        let mut draw_start = None;
        let mut retired = Vec::new();
        retire_presented_marks(&mut pending, &mut draw_start, win, &events, &mut retired);
        let (queue_out, e2e_out) = apply_sent_offsets(&retired, None);
        assert_eq!(queue_out, vec![1_000_000, 100_000_000]);
        assert_eq!(e2e_out, vec![101_000_000, 101_000_000]);
        assert_eq!(pending.len(), 1);
    }

    /// Loading frames never retire marks awaiting background filter/decompile completion, and
    /// `SENT` offsets anchor latency at `SendInput` rather than `MARK`.
    ///
    /// # Panics
    ///
    /// Panics if an unready mark (`ready_at: None`) retires on an intermediate loading frame or if
    /// `InjectTracker` fails to subtract and clamp the post-`MARK_OK` `SendInput` offset.
    #[test]
    fn loading_frames_hold_async_marks_and_sent_offsets_anchor_to_sendinput() {
        let win = gpui::WindowId::from(9);
        let t0 = now_instant();
        let ms = |n: u64| t0 + Duration::from_millis(n);
        let mut pending = VecDeque::from([PendingInputMark {
            id: 42,
            injected_at: ms(0),
            arrived_at: ms(5),
            ready_at: None,
            wait: MarkWait::Decompile(gpui::EntityId::from(1_u64), 1),
        }]);
        let loading_frame = [
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(5)),
                invalidations: 1,
                draw_start: ms(6),
                draw_end: ms(7),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(7),
                present_end: ms(8),
                animation_interval: None,
            }),
        ];
        let mut draw_start = None;
        let mut retired = Vec::new();
        retire_presented_marks(
            &mut pending,
            &mut draw_start,
            win,
            &loading_frame,
            &mut retired,
        );
        assert!(retired.is_empty());
        assert_eq!(pending.len(), 1);

        pending[0].ready_at = Some(ms(15));
        pending[0].wait = MarkWait::Immediate;
        let final_frame = [
            gpui::profiler::FrameEvent::Draw(gpui::profiler::FrameTiming {
                window_id: win,
                dirty_at: Some(ms(15)),
                invalidations: 1,
                draw_start: ms(16),
                draw_end: ms(18),
                refresh_interval: None,
                signal_at: None,
                phases: gpui::profiler::DrawPhases::default(),
            }),
            gpui::profiler::FrameEvent::Present(gpui::profiler::PresentTiming {
                window_id: win,
                present_start: ms(18),
                present_end: ms(20),
                animation_interval: None,
            }),
        ];
        retire_presented_marks(
            &mut pending,
            &mut draw_start,
            win,
            &final_frame,
            &mut retired,
        );
        assert!(pending.is_empty());
        let tracker = InjectTracker::default();
        tracker.record_sent_offset(42, 3_000_000);
        let (queue_out, e2e_out) = apply_sent_offsets(&retired, Some(&tracker));
        assert_eq!(queue_out, vec![2_000_000]);
        assert_eq!(e2e_out, vec![17_000_000]);
    }

    /// `CallTargetTracker` re-announces targets after `navigate_back` or missed clicks and caps retries.
    ///
    /// # Panics
    ///
    /// Panics if recovery suppresses `CALL_TARGET` at an unchanged click count or retries unboundedly.
    #[test]
    fn call_target_tracker_reannounces_after_recovery_and_caps_retries() {
        let t0 = now_instant();
        let mut tracker = CallTargetTracker::new();
        assert_eq!(tracker.decide_visible(0, t0), TargetDecision::Emit);
        assert_eq!(
            tracker.decide_visible(0, t0 + Duration::from_millis(20)),
            TargetDecision::Wait
        );
        assert!(tracker.note_back(true));
        assert_eq!(
            tracker.decide_visible(0, t0 + Duration::from_millis(30)),
            TargetDecision::Emit
        );
        for step in 1..8_u64 {
            assert_eq!(
                tracker.decide_visible(0, t0 + Duration::from_millis(1100 * step)),
                TargetDecision::Emit
            );
        }
        assert_eq!(
            tracker.decide_visible(0, t0 + Duration::from_millis(9000)),
            TargetDecision::Abort
        );
        assert_eq!(
            tracker.decide_visible(1, t0 + Duration::from_millis(9010)),
            TargetDecision::Emit
        );
    }
}
