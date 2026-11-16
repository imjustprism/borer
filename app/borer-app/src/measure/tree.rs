//! The call tree phase: notepad's call tree opened one closed node after another until 200
//! expansions asked the engine.
//!
//! Each is timed from the expand to the first frame drawn after its level is in the tree.
//! An expansion whose level was kept asks the engine nothing and
//! is timed apart.

use std::cmp::Reverse;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use borer_engine::cancel::Cancel;
use gpui::{Context, Entity, Subscription, Window};
use workspace::dock::DockPosition;

use super::{Harness, Prepared, SYSTEM_NOTEPAD, nanos, now_instant, say, sorted_quantiles_ms};
use crate::call_tree::{CallTree, Shape};
use crate::call_tree_panel::{CallTreePanel, PANEL};
use crate::worker::{LoadedBinary, Sources, load_binary_blocking, ui_engine_calls};

/// Expansions asking the engine the phase times.
const EXPANSIONS: usize = 200;

/// Where an expansion's level came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Took {
    /// The engine was asked for it in the background.
    Engine,
    /// The tree had kept it.
    Kept,
}

/// State of the call tree phase, carried from one expansion to the next.
pub(super) struct TreeRun {
    /// Cancel flag of the phase owning this run.
    cancel: Cancel,
    /// The tree's root.
    root: u64,
    /// When the expansion waiting for its frame began and where its level came from;
    /// `None` for the root's own read, which is not timed.
    since: Option<(Instant, Took)>,
    /// Whether the frame after the latest answer is awaited.
    painting: bool,
    /// First row the next expansion is looked for from.
    cursor: usize,
    /// Expand-to-paint times in nanoseconds of the expansions that asked the engine.
    asked: Vec<u64>,
    /// Expand-to-paint times in nanoseconds of the expansions of kept levels.
    kept: Vec<u64>,
    /// Looks at the tree again whenever the panel changes.
    _observe: Subscription,
}

/// Loads notepad and picks the call tree's root: the listed function calling the most
/// others, the lowest entry among equals.
///
/// # Arguments
///
/// * `cancel` - Cooperative cancel flag of the phase.
///
/// # Errors
///
/// Returns an error when notepad does not load or lists no function.
pub(super) fn prepare_tree(cancel: &Cancel) -> anyhow::Result<Prepared> {
    cancel.within(|| {
        let loaded = load_binary_blocking(
            PathBuf::from(SYSTEM_NOTEPAD),
            &Sources::default(),
            Vec::new(),
        )?;
        let root = loaded
            .initial_rows
            .rows
            .iter()
            .max_by_key(|row| (row.callees, Reverse(row.entry)))
            .map(|row| row.entry)
            .ok_or_else(|| anyhow::anyhow!("{SYSTEM_NOTEPAD} lists no function"))?;
        Ok(Prepared::Tree(loaded, root))
    })
}

/// Returns the first closed node row of `tree` at or after `from`.
///
/// # Arguments
///
/// * `tree` - The tree.
/// * `from` - Zero-based row index to look from.
fn next_closed(tree: &CallTree, from: usize) -> Option<usize> {
    let rows = tree.rows().get(from..)?;
    let k = rows
        .iter()
        .position(|row| tree.shape(row) == Some(Shape::Closed))?;
    from.checked_add(k)
}

/// Returns `(p50, p95, p99, max, n)` of `samples` as a protocol fragment named by `prefix`.
///
/// # Arguments
///
/// * `prefix` - The fields' prefix.
/// * `samples` - Times in nanoseconds, sorted in place.
fn quantiles(prefix: &str, samples: &mut [u64]) -> String {
    let (p50, p95, p99, max, n) = sorted_quantiles_ms(samples);
    format!(
        "{prefix}samples={n} {prefix}p50_ms={p50:.3} {prefix}p95_ms={p95:.3} \
{prefix}p99_ms={p99:.3} {prefix}max_ms={max:.3}"
    )
}

impl Harness {
    /// Opens `loaded` as the binary of the measured window, roots the call tree at `root`,
    /// shows its panel, and times each expansion once the root's level is in.
    ///
    /// # Arguments
    ///
    /// * `cancel` - Cancel flag of the phase.
    /// * `(loaded, root)` - Notepad and the tree's root.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    pub(super) fn start_tree(
        &mut self,
        cancel: Cancel,
        (loaded, root): (Arc<LoadedBinary>, u64),
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        self.binary
            .update(cx, |binary, cx| binary.show_loaded(loaded.clone(), cx));
        let binary = self.binary.clone();
        let panel = self.workspace.update(cx, |workspace, cx| {
            if workspace.panel::<CallTreePanel>(cx).is_none() {
                (PANEL.add)(workspace, &binary, DockPosition::Bottom, window, cx);
            }
            workspace.panel::<CallTreePanel>(cx)
        });
        let Some(panel) = panel else {
            self.fail(anyhow::anyhow!("the call tree panel did not dock"), cx);
            return;
        };
        self.workspace.update(cx, |workspace, cx| {
            workspace.open_panel::<CallTreePanel>(window, cx);
        });
        let observe = cx.observe_in(&panel, window, |this, panel, window, cx| {
            this.tree_changed(&panel, window, cx);
        });
        self.tree_run = Some(TreeRun {
            cancel,
            root,
            since: None,
            painting: false,
            cursor: 0,
            asked: Vec::with_capacity(EXPANSIONS),
            kept: Vec::new(),
            _observe: observe,
        });
        cx.on_next_frame(window, move |_, _, cx| {
            panel.update(cx, |panel, cx| panel.set_root(&loaded, root, cx));
        });
    }

    /// Awaits the next frame once the tree has every level it asked for.
    ///
    /// # Arguments
    ///
    /// * `panel` - The call tree panel.
    /// * `window` - Window driving frame callbacks.
    /// * `cx` - Harness context.
    fn tree_changed(
        &mut self,
        panel: &Entity<CallTreePanel>,
        window: &mut Window,
        cx: &mut Context<'_, Self>,
    ) {
        let answered = panel
            .read(cx)
            .tree()
            .is_some_and(|tree| tree.reading() == 0);
        let Some(run) = self.tree_run.as_mut() else {
            return;
        };
        if run.painting || !answered || run.cancel.is_raised() {
            return;
        }
        run.painting = true;
        let panel = panel.clone();
        cx.on_next_frame(window, move |this, _, cx| this.tree_painted(&panel, cx));
    }

    /// Records the expansion whose rows the last frame drew and opens the next closed node,
    /// or reports once [`EXPANSIONS`] asked the engine or no node is left closed.
    ///
    /// # Arguments
    ///
    /// * `panel` - The call tree panel.
    /// * `cx` - Harness context.
    fn tree_painted(&mut self, panel: &Entity<CallTreePanel>, cx: &mut Context<'_, Self>) {
        let now = now_instant();
        let Some(cursor) = self.tree_run.as_ref().map(|run| run.cursor) else {
            return;
        };
        let next = panel
            .read(cx)
            .tree()
            .and_then(|tree| next_closed(tree, cursor));
        let Some(run) = self.tree_run.as_mut() else {
            return;
        };
        if run.cancel.is_raised() {
            return;
        }
        run.painting = false;
        if let Some((since, took)) = run.since.take() {
            let ns = nanos(now.saturating_duration_since(since));
            match took {
                Took::Engine => run.asked.push(ns),
                Took::Kept => run.kept.push(ns),
            }
        }
        let Some(ix) = next.filter(|_| run.asked.len() < EXPANSIONS) else {
            let line = format!(
                "MEASURE_TREE {} {} root={:#x} ui_engine_calls={}",
                quantiles("", &mut run.asked),
                quantiles("kept_", &mut run.kept),
                run.root,
                ui_engine_calls()
            );
            match say(&line) {
                Ok(()) => cx.quit(),
                Err(err) => self.fail(err, cx),
            }
            return;
        };
        run.cursor = ix.saturating_add(1);
        let started = now_instant();
        let reading = panel.update(cx, |panel, cx| {
            panel.toggle(ix, cx);
            panel.tree().map_or(0, CallTree::reading)
        });
        let took = if reading > 0 {
            Took::Engine
        } else {
            Took::Kept
        };
        if let Some(run) = self.tree_run.as_mut() {
            run.since = Some((started, took));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::next_closed;
    use crate::call_tree::tests::{MAIN, answer_asked, tree_program};
    use crate::call_tree::{CallTree, Direction, Virtuals};

    /// The phase opens closed nodes in row order and skips the open root, leaves and
    /// cycles.
    ///
    /// # Panics
    ///
    /// Panics if a row other than the first closed one from the cursor is picked.
    #[test]
    fn the_phase_opens_the_next_closed_node() {
        let loaded = tree_program();
        let mut tree = CallTree::new(MAIN, Direction::Callees, Virtuals::Hidden);
        assert_eq!(next_closed(&tree, 0), Some(0));
        let asked = tree.expand(0);
        answer_asked(&mut tree, &loaded, asked);
        assert_eq!(next_closed(&tree, 0), Some(3));
        let asked = tree.expand(3);
        answer_asked(&mut tree, &loaded, asked);
        assert_eq!(next_closed(&tree, 0), None);
        assert_eq!(next_closed(&tree, 99), None);
    }
}
