//! The scroll phases: 100,000 function rows and 1,000,000 decompile lines scrolled a
//! few rows each frame for 10 seconds, with gpui's frame histograms read around the run.

use std::time::{Duration, Instant};

use borer_engine::cancel::Cancel;
use gpui::{Context, Window};

use super::{
    Harness, MeasurePhase, Prepared, TARGET_CODE_LINES, TARGET_LIST_ROWS, nanos, now_instant,
    ns_to_ms, say, sorted_quantiles_ms,
};
use crate::decompile_item::open_lines;
use crate::worker::ui_engine_calls;

/// Number of rows or lines advanced on each animation frame during scroll benchmarks.
const SCROLL_STEP_PER_FRAME: usize = 7;

/// Frames drawn before a scroll run starts recording.
const WARMUP_FRAMES: u8 = 8;

/// Duration of each scripted scroll benchmark run.
const SCROLL_DURATION: Duration = Duration::from_secs(10);

/// State of one 10-second scripted scroll, carried from frame to frame.
struct ScrollRun {
    /// Measurement generation owning this run.
    ticket: u64,
    /// Cooperative cancel flag owning this run.
    cancel: Cancel,
    /// `true` to scroll the code view, `false` the function table.
    code: bool,
    /// Label naming the loaded binary for the report.
    source: String,
    /// Items before repetition.
    base: usize,
    /// Items the scrolled list shows.
    items: usize,
    /// Whether the code scroll follows this one.
    then_code: bool,
    /// Warmup frames remaining before recording begins.
    warmup: u8,
    /// Snapshot captured immediately after warmup.
    before: Option<gpui::profiler::FrameDurationSnapshot>,
    /// Start of the recorded window.
    started: Option<Instant>,
    /// Timestamp of the previous frame.
    prev: Option<Instant>,
    /// Current scroll target index.
    ix: usize,
    /// Recorded frame-to-frame durations in nanoseconds.
    intervals: Vec<u64>,
}

impl Harness {
    /// Shows what `prepared` holds in the workspace and starts its run on the next frame.
    ///
    /// # Arguments
    ///
    /// * `ticket` - Generation of the phase.
    /// * `cancel` - Cancel flag of the phase.
    /// * `prepared` - The phase's background preparation.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    pub(super) fn start(
        &mut self,
        ticket: u64,
        cancel: Cancel,
        prepared: Prepared,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        cx.activate(true);
        window.activate_window();
        let (loaded, rows) = match &prepared {
            Prepared::List(ready, _) => (ready.loaded.clone(), ready.rows.clone()),
            Prepared::Code(corpus) => (corpus.loaded.clone(), corpus.loaded.initial_rows.clone()),
            Prepared::Input(loaded, _) => (loaded.clone(), loaded.initial_rows.clone()),
        };
        if let Some(panel) = self.panel(cx) {
            panel.update(cx, |panel, cx| panel.show(loaded, rows, window, cx));
        }
        let (code, source, base, items, then_code) = match prepared {
            Prepared::List(ready, then_code) => {
                let source = format!(
                    "{} ({:.2}s)",
                    ready.loaded.path.display(),
                    ready.analyze_secs
                );
                (false, source, ready.base_rows, TARGET_LIST_ROWS, then_code)
            }
            Prepared::Code(corpus) => {
                let source = corpus.loaded.path.display().to_string();
                self.workspace.update(cx, |workspace, cx| {
                    open_lines(workspace, corpus.loaded, corpus.code, window, cx);
                });
                (true, source, corpus.base_lines, TARGET_CODE_LINES, false)
            }
            Prepared::Input(loaded, entry) => {
                self.start_input(ticket, cancel, loaded, entry, window, cx);
                return;
            }
        };
        let run = ScrollRun {
            ticket,
            cancel,
            code,
            source,
            base,
            items,
            then_code,
            warmup: WARMUP_FRAMES,
            before: None,
            started: None,
            prev: None,
            ix: 0,
            intervals: Vec::with_capacity(2048),
        };
        cx.on_next_frame(window, move |this, window, cx| {
            this.scroll_step(run, window, cx);
        });
    }

    /// Scrolls one step of `run`, recording frame intervals, until 10 seconds pass.
    ///
    /// # Arguments
    ///
    /// * `run` - The scroll's state.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    fn scroll_step(&mut self, mut run: ScrollRun, window: &mut Window, cx: &mut Context<'_, Self>) {
        if !self.epoch.is_current(run.ticket, &run.cancel) {
            return;
        }
        let now = now_instant();
        if run.warmup > 0 {
            run.warmup -= 1;
            if run.warmup == 0 {
                run.before = Some(window.frame_duration_snapshot());
                run.started = Some(now);
                run.prev = Some(now);
            }
        } else {
            if let Some(prev) = run.prev.replace(now) {
                run.intervals.push(nanos(now.duration_since(prev)));
            }
            if run
                .started
                .is_some_and(|t0| now.duration_since(t0) >= SCROLL_DURATION)
            {
                self.finish_scroll(run, window, cx);
                return;
            }
        }
        run.ix = run.ix.saturating_add(SCROLL_STEP_PER_FRAME) % run.items.max(1);
        let ix = run.ix;
        if run.code {
            if let Some(item) = self.item(cx) {
                item.update(cx, |item, cx| {
                    item.scroll_to(ix);
                    cx.notify();
                });
            }
        } else if let Some(panel) = self.panel(cx) {
            panel.update(cx, |panel, cx| {
                panel.scroll_to(ix, cx);
                cx.notify();
            });
        }
        cx.on_next_frame(window, move |this, window, cx| {
            this.scroll_step(run, window, cx);
        });
    }

    /// Prints the report of a finished scroll, then runs the code scroll or quits.
    ///
    /// # Arguments
    ///
    /// * `run` - The finished scroll.
    /// * `window` - Window providing the closing snapshot.
    /// * `cx` - Harness context.
    fn finish_scroll(
        &mut self,
        mut run: ScrollRun,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let Some(before) = run.before.take() else {
            self.fail(anyhow::anyhow!("scroll run ended before its warmup"), cx);
            return;
        };
        let after = window.frame_duration_snapshot();
        let kind = if run.code { "code" } else { "list" };
        let report = scroll_report(
            kind,
            &run.source,
            run.base,
            run.items,
            &before,
            &after,
            &mut run.intervals,
        )
        .and_then(|line| say(&line));
        match report {
            Err(err) => self.fail(err, cx),
            Ok(()) if run.then_code => self.begin(MeasurePhase::CodeScroll, cx),
            Ok(()) => cx.quit(),
        }
    }
}

/// Summarizes frame work recorded between two snapshots, across refresh intervals.
///
/// # Arguments
///
/// * `before` - Profiler snapshot recorded immediately after warmup.
/// * `after` - Profiler snapshot recorded after the 10-second scroll loop.
///
/// # Returns
///
/// `(work_n, work_p50_ms, work_p95_ms, work_p99_ms, work_max_ms, refresh_ms)`.
///
/// # Errors
///
/// Returns an error when the profiler's histograms cannot be subtracted or added, so a
/// failed step never drops samples silently.
fn frame_work(
    before: &gpui::profiler::FrameDurationSnapshot,
    after: &gpui::profiler::FrameDurationSnapshot,
) -> anyhow::Result<(u64, f64, f64, f64, f64, f64)> {
    let mut combined = None;
    let mut max_refresh_ns: u64 = 0;
    for post in &after.by_refresh_interval {
        let pre = before
            .by_refresh_interval
            .iter()
            .find(|pre| pre.refresh_interval == post.refresh_interval);
        let mut work = post.work.clone();
        if let Some(pre) = pre {
            work.subtract(&pre.work)?;
        }
        let drawn = post
            .frames_drawn
            .saturating_sub(pre.map_or(0, |p| p.frames_drawn));
        if drawn == 0 && work.is_empty() {
            continue;
        }
        if let Some(interval) = post.refresh_interval {
            max_refresh_ns = max_refresh_ns.max(nanos(interval));
        }
        match &mut combined {
            None => combined = Some(work),
            Some(acc) => acc.add(&work)?,
        }
    }
    let refresh_ms = ns_to_ms(max_refresh_ns);
    let Some(acc) = combined else {
        return Ok((0, 0.0, 0.0, 0.0, 0.0, refresh_ms));
    };
    Ok((
        acc.len(),
        ns_to_ms(acc.value_at_quantile(0.50)),
        ns_to_ms(acc.value_at_quantile(0.95)),
        ns_to_ms(acc.value_at_quantile(0.99)),
        ns_to_ms(acc.max()),
        refresh_ms,
    ))
}

/// Formats frame-duration and interval snapshots into one `MEASURE_SCROLL` protocol line.
///
/// # Arguments
///
/// * `kind` - `"list"` or `"code"`.
/// * `source` - Label naming the loaded binary.
/// * `base_items` - Unreplicated item count.
/// * `virtual_items` - Item count the scrolled list shows.
/// * `before` - Profiler snapshot recorded immediately after warmup.
/// * `after` - Profiler snapshot recorded after the 10-second scroll loop.
/// * `manual_intervals_ns` - Frame-to-frame durations collected via [`now_instant`].
///
/// # Errors
///
/// Returns an error when a histogram subtraction or addition fails.
pub(super) fn scroll_report(
    kind: &str,
    source: &str,
    base_items: usize,
    virtual_items: usize,
    before: &gpui::profiler::FrameDurationSnapshot,
    after: &gpui::profiler::FrameDurationSnapshot,
    manual_intervals_ns: &mut [u64],
) -> anyhow::Result<String> {
    let mut draw = after.draw_duration_histogram.clone();
    draw.subtract(&before.draw_duration_histogram)?;
    let mut dirty = after.dirty_to_present_histogram.clone();
    dirty.subtract(&before.dirty_to_present_histogram)?;
    let mut present = after.present_interval_histogram.clone();
    present.subtract(&before.present_interval_histogram)?;
    let (wn, wp50, wp95, wp99, wmax, refresh_ms) = frame_work(before, after)?;
    let (mp50, mp95, mp99, mmax, mcount) = sorted_quantiles_ms(manual_intervals_ns);
    let replicated = base_items < virtual_items;
    Ok(format!(
        "MEASURE_SCROLL kind={kind} source={source:?} base_items={base_items} virtual_items={virtual_items} replicated={replicated} \
draw_n={} draw_p50_ms={:.3} draw_p95_ms={:.3} draw_p99_ms={:.3} draw_max_ms={:.3} \
work_n={wn} work_p50_ms={wp50:.3} work_p95_ms={wp95:.3} work_p99_ms={wp99:.3} work_max_ms={wmax:.3} refresh_ms={refresh_ms:.3} \
dirty_n={} dirty_p50_ms={:.3} dirty_p95_ms={:.3} dirty_p99_ms={:.3} dirty_max_ms={:.3} \
present_n={} present_p50_ms={:.3} present_p95_ms={:.3} present_p99_ms={:.3} present_max_ms={:.3} \
manual_n={mcount} manual_p50_ms={mp50:.3} manual_p95_ms={mp95:.3} manual_p99_ms={mp99:.3} manual_max_ms={mmax:.3} \
ui_engine_calls={}",
        draw.len(),
        ns_to_ms(draw.value_at_quantile(0.50)),
        ns_to_ms(draw.value_at_quantile(0.95)),
        ns_to_ms(draw.value_at_quantile(0.99)),
        ns_to_ms(draw.max()),
        dirty.len(),
        ns_to_ms(dirty.value_at_quantile(0.50)),
        ns_to_ms(dirty.value_at_quantile(0.95)),
        ns_to_ms(dirty.value_at_quantile(0.99)),
        ns_to_ms(dirty.max()),
        present.len(),
        ns_to_ms(present.value_at_quantile(0.50)),
        ns_to_ms(present.value_at_quantile(0.95)),
        ns_to_ms(present.value_at_quantile(0.99)),
        ns_to_ms(present.max()),
        ui_engine_calls(),
    ))
}
