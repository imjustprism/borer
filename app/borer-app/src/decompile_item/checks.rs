//! A code tab's check gutter: grading its lines in the background from the session's
//! checks, the evidence under a line, stepping between wrong blocks and rechecking a block.

use std::collections::BTreeMap;
use std::sync::Arc;

use borer_engine::analysis::decompile::replay::{Grade, Prior, Rechecked};
use gpui::{App, Context, Entity};
use workspace::Workspace;

use super::DecompileItem;
use crate::binary::Binary;
use crate::check_marks::{Marks, Toward, grade_word, insert_evidence, line_block};
use crate::code_view::CodeLines;
use crate::linear_item::LinearItem;
use crate::worker::{State, marks_blocking, recheck_blocking};

/// States a recheck tries a block from; the engine holds it within its bounds.
pub(super) const RECHECK_STATES: u32 = 64;

/// Returns the code tab an action of the gutter acts on: the active code tab, else the
/// lines of the active linear listing.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `cx` - Application context.
#[must_use]
pub(super) fn active_code(workspace: &Workspace, cx: &App) -> Option<Entity<DecompileItem>> {
    workspace.active_item_as::<DecompileItem>(cx).or_else(|| {
        let linear = workspace.active_item_as::<LinearItem>(cx)?;
        Some(linear.read(cx).code().clone())
    })
}

/// Runs `act` on the code tab a gutter action acts on ([`active_code`]), or says on the
/// status line that the action needs one.
///
/// # Arguments
///
/// * `workspace` - The window's workspace.
/// * `binary` - The window's binary, whose status line says so.
/// * `cx` - Application context.
/// * `act` - What to do on the tab.
pub(super) fn act_on_code(
    workspace: &Workspace,
    binary: &Entity<Binary>,
    cx: &mut App,
    act: impl FnOnce(&mut DecompileItem, &mut Context<'_, DecompileItem>),
) {
    match active_code(workspace, cx) {
        Some(item) => item.update(cx, act),
        None => {
            let why = "This acts on a decompile, listing or linear tab; none is active.";
            binary.update(cx, |b, cx| b.set_status(why.to_owned(), cx));
        }
    }
}

/// Returns what the status line says of a recheck of block `start`: its grade from its
/// states, and what its record took the place of.
///
/// # Arguments
///
/// * `start` - The block's start.
/// * `(grade, states)` - The recheck's grade and the states it tried.
/// * `merged` - What the session did with the record, `None` with no check to put it in.
#[must_use]
pub(super) fn recheck_said(
    start: u64,
    (grade, states): (Grade, u32),
    merged: Option<Rechecked>,
) -> String {
    let said = format!(
        "Block {start:#x} rechecked from {states} states: {}",
        grade_word(grade)
    );
    let prior = |p: Prior| {
        let whose = if p.rechecked {
            "the earlier recheck"
        } else {
            "the check"
        };
        format!("{whose}: {} from {} states", grade_word(p.grade), p.states)
    };
    match merged {
        None => format!("{said}; the function has no check to hold it."),
        Some(Rechecked::Added) => format!("{said}."),
        Some(Rechecked::Replaced(p)) => format!("{said}; it replaced {}.", prior(p)),
        Some(Rechecked::KeptWrong(p)) => format!("{said}; it stays wrong, as {}.", prior(p)),
    }
}

impl DecompileItem {
    /// Grades `code`, the lines shown now, in the background, from the session's checks:
    /// those rechecks left, then those the earlier marks of this state hold, then the
    /// engine's; the marks shown stay until the new ones arrive.
    ///
    /// # Arguments
    ///
    /// * `code` - The shown lines.
    /// * `cx` - Item context.
    pub(super) fn grade_lines(&mut self, code: Arc<CodeLines>, cx: &mut Context<'_, Self>) {
        let loaded = self.loaded.clone();
        let state = loaded.state();
        let mut held: BTreeMap<_, _> = self
            .marks
            .as_ref()
            .filter(|m| *m.state() == state)
            .map(|m| m.checks().clone())
            .unwrap_or_default();
        let rechecked = self.binary.read(cx).rechecks(&state);
        held.extend(rechecked.map(|(f, check)| (f, check.clone())));
        let label = self.entry.map_or_else(
            || "Grading lines".to_owned(),
            |at| format!("Grading {at:#x}"),
        );
        let work = move || marks_blocking(&loaded, &code, &held);
        self.marks_job.run(label, cx, work, |item, marks, cx| {
            item.marks = Some(marks);
            item.paint(true, cx);
            if let Some((row, _, _)) = item.evidence {
                item.hide_check(cx);
                item.show_check(Some(row), cx);
            }
            cx.notify();
        });
    }

    /// Shows the evidence behind the mark of shown line `row`, else of the cursor's line,
    /// in a block under it, or hides it when it is shown there already; the status line
    /// says why a line has none.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based shown line, `None` for the cursor's.
    /// * `cx` - Item context.
    pub fn show_check(&mut self, row: Option<usize>, cx: &mut Context<'_, Self>) {
        let Some(row) = row.or_else(|| Some(self.cursor(cx)?.0)) else {
            return;
        };
        let here = self.evidence.as_ref().is_some_and(|(at, _, _)| *at == row);
        self.hide_check(cx);
        if here {
            return;
        }
        let Some((marks, code)) = self.marks().zip(self.code.as_deref()) else {
            self.say("The lines are still being graded.".to_owned(), cx);
            return;
        };
        let Some(said) = marks.evidence(code, row) else {
            let why = if line_block(code, row).is_some() {
                "This line's function is still being checked."
            } else {
                "This line stands for no block, so it has no grade."
            };
            self.say(why.to_owned(), cx);
            return;
        };
        let block = self
            .editor
            .update(cx, |editor, cx| insert_evidence(editor, row, &said, cx));
        self.evidence = block.map(|block| (row, said, block));
    }

    /// Hides the evidence shown under a line, if any.
    ///
    /// # Arguments
    ///
    /// * `cx` - Item context.
    pub(super) fn hide_check(&mut self, cx: &mut Context<'_, Self>) {
        if let Some((_, _, block)) = self.evidence.take() {
            self.editor.update(cx, |editor, cx| {
                editor.remove_blocks([block].into_iter().collect(), None, cx);
            });
        }
    }

    /// Replays the block of the cursor's line from `states` states in the background, as
    /// the answer's check seeds them, and puts the record in the session's check of its
    /// function, which every view of that function then shows.
    ///
    /// New lines in the tab or leaving it drop the recheck, and a record that comes back
    /// for an earlier state than the tab's is dropped too; the status line says what the
    /// record took the place of, and when a running recheck is dropped for this one.
    ///
    /// # Arguments
    ///
    /// * `states` - States to try, which the engine holds within its bounds.
    /// * `cx` - Item context.
    pub fn recheck(&mut self, states: u32, cx: &mut Context<'_, Self>) {
        let row = self.cursor(cx).map(|(row, _)| row);
        let block = row
            .zip(self.code.as_deref())
            .and_then(|(r, c)| line_block(c, r));
        let Some(block) = block else {
            let why = "This line stands for no block to recheck.";
            self.say(why.to_owned(), cx);
            return;
        };
        let (loaded, start) = (self.loaded.clone(), block.start);
        let state = loaded.state();
        let mut label = format!("Rechecking {start:#x}");
        if self.recheck_job.is_running() {
            label.push_str("; the recheck running before is dropped");
        }
        self.say(label.clone(), cx);
        let work = move || recheck_blocking(&loaded, block, states);
        self.rechecking = Some(start);
        self.recheck_job
            .run(label, cx, work, move |item, done, cx| {
                item.rechecking = None;
                let Some((record, check)) = done else {
                    item.say(
                        format!("The engine could not recheck block {start:#x}."),
                        cx,
                    );
                    return;
                };
                if item.loaded.state() != state {
                    let why = format!(
                        "The recheck of block {start:#x} was of an earlier state, so it is dropped."
                    );
                    item.say(why, cx);
                    return;
                }
                let tried = (record.grade(), record.states());
                let at = (state, block.function);
                let binary = item.binary.clone();
                let merged = binary.update(cx, |b, cx| b.put_recheck(at, &check, record, cx));
                item.say(recheck_said(start, tried, merged), cx);
            });
    }

    /// Grades the lines again when a recheck changed the check of a function of the tab's
    /// state, and tells the views that follow the tab.
    ///
    /// # Arguments
    ///
    /// * `state` - The program and overlay state the recheck ran under.
    /// * `cx` - Item context.
    pub(super) fn rechecked(&mut self, state: &State, cx: &mut Context<'_, Self>) {
        if *state != self.loaded.state() {
            return;
        }
        if let Some(code) = self.code.clone() {
            self.grade_lines(code, cx);
        }
        cx.notify();
    }

    /// Stops the running recheck, if any, and says on the status line why it stopped.
    ///
    /// # Arguments
    ///
    /// * `why` - What stopped it.
    /// * `cx` - Item context.
    pub(super) fn drop_recheck(&mut self, why: &str, cx: &mut Context<'_, Self>) {
        self.recheck_job.stop();
        if let Some(start) = self.rechecking.take() {
            self.say(
                format!("The recheck of block {start:#x} stopped: {why}."),
                cx,
            );
        }
    }

    /// Returns the grades of the shown lines, once they are in for the tab's state: marks
    /// of an earlier state show nothing until the lines are graded again.
    #[must_use]
    pub fn marks(&self) -> Option<&Marks> {
        self.marks
            .as_ref()
            .filter(|m| self.loaded.is_state(m.state()))
    }

    /// Returns the evidence shown under a line, `None` when none is.
    #[must_use]
    pub fn evidence(&self) -> Option<&str> {
        self.evidence.as_ref().map(|(_, said, _)| said.as_str())
    }

    /// Moves to the first line of the next wrong block from the cursor's line, going
    /// round past either end; the status line says when no line is wrong or the lines are
    /// still being graded.
    ///
    /// # Arguments
    ///
    /// * `toward` - Which way to look.
    /// * `cx` - Item context.
    pub fn step_wrong(&mut self, toward: Toward, cx: &mut Context<'_, Self>) {
        let graded = self
            .marks()
            .filter(|m| self.code.as_ref().is_some_and(|code| m.is_for(code)));
        let Some(marks) = graded else {
            self.say("The lines are still being graded.".to_owned(), cx);
            return;
        };
        let from = self.cursor(cx).map_or(0, |(row, _)| row);
        match marks.next_wrong(from, toward) {
            Some(row) => self.jump_to_line(row, cx),
            None => self.say("No line of this tab is marked wrong.".to_owned(), cx),
        }
    }

    /// Returns the grade shown line `row` is marked with, `None` while the lines are graded
    /// and for a line with no mark.
    ///
    /// # Arguments
    ///
    /// * `row` - Zero-based shown line.
    #[must_use]
    pub fn grade(&self, row: usize) -> Option<Grade> {
        self.marks()?.grade(self.code.as_deref()?, row)
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test; gpui::test hides each body in an undocumented fn"
)]
mod tests {
    use std::sync::Arc;

    use borer_engine::analysis::decompile::replay::Grade;
    use gpui::{Entity, TestAppContext, VisualTestContext};
    use workspace::Item as _;

    use super::RECHECK_STATES;
    use crate::actions::NextWrongBlock;
    use crate::app_view::tests::{binary_in, init, open};
    use crate::binary::{Binary, BinaryEvent, Revision as _};
    use crate::check_marks::line_block;
    use crate::check_marks::tests::{FLOAT_BETWEEN, STORE, one_function, wrong_at};
    use crate::decompile_item::tests::{open_tab, put_cursor};
    use crate::decompile_item::{DecompileItem, Form};
    use crate::linear_item::tests::{open_linear, settle};
    use crate::worker::{State, check_blocking, run_engine};

    /// The entry of the one function of [`one_function`].
    const ENTRY: u64 = 0x1000;

    /// Puts the cursor of `tab` on its first line written from a block and returns that
    /// line.
    fn on_a_block(tab: &Entity<DecompileItem>, cx: &mut VisualTestContext) -> usize {
        let row = tab.read_with(cx, |item, _| {
            let code = item.code().unwrap();
            (0..code.len()).find(|&r| line_block(code, r).is_some())
        });
        let row = row.unwrap();
        put_cursor(tab, (row, 0), cx);
        row
    }

    /// Returns the status line of `binary`.
    fn status(binary: &Entity<Binary>, cx: &mut VisualTestContext) -> String {
        binary.read_with(cx, |binary, _| binary.status().to_owned())
    }

    /// A recheck lands in the session: the tab's marks and the function's other view grade
    /// by it, its record tried the states asked for and the evidence says so, a second
    /// recheck gives the same record, and it says it replaced the first.
    #[gpui::test]
    fn a_recheck_reaches_every_view_and_a_second_replaces_the_first(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let (workspace, binary) = (app.workspace, app.binary);
        let loaded = one_function(&STORE);
        let state = loaded.state();
        let listing = open_tab(&workspace, &loaded, (ENTRY, Form::Listing), cx);
        let row = on_a_block(&listing, cx);
        listing.update(cx, |item, cx| item.recheck(RECHECK_STATES, cx));
        cx.run_until_parked();
        let held = binary.read_with(cx, |b, _| b.rechecked(&state, ENTRY));
        let held = held.expect("the session holds the recheck");
        let first = (*held).as_ref().unwrap().record(ENTRY).cloned().unwrap();
        assert_eq!(first.states(), RECHECK_STATES);
        let said = status(&binary, cx);
        assert!(said.contains("it replaced the check"), "{said}");
        let marked = listing.read_with(cx, |item, _| {
            Arc::ptr_eq(item.marks().unwrap().checks().get(&ENTRY).unwrap(), &held)
        });
        assert!(marked, "the tab grades by the session's check");
        listing.update(cx, |item, cx| item.show_check(Some(row), cx));
        let shown = listing.read_with(cx, |item, _| item.evidence().map(str::to_owned));
        let shown = shown.unwrap();
        assert!(shown.contains("rechecked from up to 64 states"), "{shown}");
        let decompile = open_tab(&workspace, &loaded, (ENTRY, Form::Decompile), cx);
        let marked = decompile.read_with(cx, |item, _| {
            Arc::ptr_eq(item.marks().unwrap().checks().get(&ENTRY).unwrap(), &held)
        });
        assert!(marked, "the other view grades by the session's check");
        let listing = open_tab(&workspace, &loaded, (ENTRY, Form::Listing), cx);
        on_a_block(&listing, cx);
        listing.update(cx, |item, cx| item.recheck(RECHECK_STATES, cx));
        cx.run_until_parked();
        let said = status(&binary, cx);
        assert!(said.contains("it replaced the earlier recheck"), "{said}");
        let again = binary
            .read_with(cx, |b, _| b.rechecked(&state, ENTRY))
            .unwrap();
        let again = (*again).as_ref().unwrap().record(ENTRY).cloned().unwrap();
        assert_eq!(
            again, first,
            "a recheck from the answer's seed is deterministic"
        );
    }

    /// Leaving the tab drops a running recheck and says so, and an edit landing before it
    /// answers drops it too: the session holds no record of either.
    #[gpui::test]
    fn a_recheck_is_dropped_by_leaving_the_tab_and_by_an_edit(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let (workspace, binary) = (app.workspace, app.binary);
        let (loaded, other) = (one_function(&STORE), one_function(&FLOAT_BETWEEN));
        let tab = open_tab(&workspace, &loaded, (ENTRY, Form::Listing), cx);
        on_a_block(&tab, cx);
        tab.update_in(cx, |item, window, cx| {
            item.recheck(RECHECK_STATES, cx);
            item.deactivated(window, cx);
        });
        let said = status(&binary, cx);
        assert!(said.contains("stopped: the tab was left"), "{said}");
        cx.run_until_parked();
        let held = binary.read_with(cx, |b, _| b.rechecked(&loaded.state(), ENTRY));
        assert!(held.is_none(), "leaving the tab drops it");
        tab.update(cx, |item, cx| item.recheck(RECHECK_STATES, cx));
        binary.update(cx, |_, cx| cx.emit(BinaryEvent::Revised(other.clone())));
        cx.run_until_parked();
        for state in [&loaded, &other] {
            let held = binary.read_with(cx, |b, _| b.rechecked(&state.state(), ENTRY));
            assert!(held.is_none(), "an edit drops it");
        }
    }

    /// Two programs with a function at the same address, under the same overlay, keep
    /// their rechecks apart, and closing the binary drops them.
    #[gpui::test]
    fn rechecks_are_kept_per_program_and_dropped_on_close(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let binary = app.binary;
        let (a, b) = (one_function(&STORE), one_function(&FLOAT_BETWEEN));
        assert_eq!(a.fingerprint, b.fingerprint, "one overlay");
        let check = run_engine(|| check_blocking(&a, ENTRY));
        let at = (a.state(), ENTRY);
        binary.update(cx, |bin, cx| {
            bin.put_recheck(at, &check, wrong_at(ENTRY), cx)
        });
        let held = |state: State, cx: &mut VisualTestContext| {
            binary.read_with(cx, |bin, _| bin.rechecked(&state, ENTRY).is_some())
        };
        assert!(held(a.state(), cx));
        assert!(!held(b.state(), cx), "another program at the same address");
        binary.update(cx, |bin, cx| bin.close(cx));
        assert!(!held(a.state(), cx), "closing drops them");
    }

    /// The linear listing grades its lines under the state an edit leaves: a line the new
    /// state's check proves is proved, not graded by the old state's check, and the digest
    /// holds the marks.
    #[gpui::test]
    fn the_linear_listing_grades_under_the_state_an_edit_leaves(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let binary = binary_in(&workspace, cx);
        let (before, after) = (one_function(&STORE), one_function(&FLOAT_BETWEEN));
        let linear = open_linear(&workspace, &before, None, cx);
        settle(&linear, cx);
        let code = linear.read_with(cx, |item, _| item.code().clone());
        let graded = |cx: &mut VisualTestContext| {
            code.read_with(cx, |item, _| item.marks().map(|m| m.state().clone()))
        };
        assert_eq!(graded(cx), Some(before.state()));
        let at = |cx: &mut VisualTestContext| {
            code.read_with(cx, |item, _| {
                let lines = item.code().unwrap();
                (0..lines.len())
                    .filter(|&row| lines.get(row).and_then(|(v, l)| v.address(l)) == Some(0x100a))
                    .filter_map(|row| item.grade(row))
                    .collect::<Vec<_>>()
            })
        };
        assert_eq!(at(cx), Vec::<Grade>::new(), "no block at 0x100a before");
        binary.update(cx, |_, cx| cx.emit(BinaryEvent::Revised(after.clone())));
        settle(&linear, cx);
        assert_eq!(graded(cx), Some(after.state()));
        assert_eq!(at(cx), [Grade::Proved], "graded by the new state's check");
        let digest = code.read_with(cx, |item, cx| item.digest(cx));
        code.update(cx, |item, _| item.marks = None);
        let bare = code.read_with(cx, |item, cx| item.digest(cx));
        assert_ne!(digest, bare, "the digest holds the marks");
    }

    /// Next wrong acts on the linear listing's lines and says what it found there.
    #[gpui::test]
    fn next_wrong_acts_on_the_linear_listing(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let workspace = app.workspace;
        let binary = binary_in(&workspace, cx);
        let linear = open_linear(&workspace, &one_function(&STORE), None, cx);
        settle(&linear, cx);
        binary.update(cx, |b, cx| b.set_status("before".to_owned(), cx));
        cx.dispatch_action(NextWrongBlock);
        cx.run_until_parked();
        assert_eq!(status(&binary, cx), "No line of this tab is marked wrong.");
    }

    /// Going to the function's entry in an open decompile tab whose lines show no
    /// instruction moves the cursor to the top.
    #[gpui::test]
    fn going_to_the_entry_moves_the_cursor_to_the_top(cx: &mut TestAppContext) {
        let app_state = init(cx);
        let (app, cx) = open(&app_state, cx);
        let loaded = one_function(&STORE);
        let tab = open_tab(&app.workspace, &loaded, (ENTRY, Form::Decompile), cx);
        put_cursor(&tab, (2, 0), cx);
        tab.update(cx, |item, cx| item.go_to_address(ENTRY, cx));
        cx.update(|window, cx| window.draw(cx).clear(cx));
        let row = tab.read_with(cx, |item, cx| item.cursor(cx).map(|(row, _)| row));
        assert_eq!(row, Some(0));
    }
}
