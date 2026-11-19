//! The binary's edits: a shown plan committed by its author into the one log the change feed
//! and Undo read, and Undo and Redo stepping through that log.

use std::sync::Arc;

use borer_engine::analysis::edit::{self, Author};
use borer_engine::text;
use futures::channel::oneshot;
use gpui::Context;

use super::{Binary, Committed, LABEL_MAX};
use crate::history::{BYTES_MAX, Entry, Kind, STEPS_MAX, Way, step_blocking, whose};
use crate::worker::{LoadedBinary, Shown, commit_blocking};

impl Binary {
    /// Commits `shown`, a plan whose lines were on screen, through the engine's edit path in
    /// the background, the same path the server's annotating tools take, and shows the
    /// overlay it leaves; one entry by `author` then serves the change feed and Undo
    /// ([`crate::history::History`]), and the status line says what the commit did in the engine's words.
    ///
    /// # Arguments
    ///
    /// * `shown` - The plan.
    /// * `author` - Who made it: the person, or a model whose proposal the person accepted.
    /// * `cx` - Binary context.
    ///
    /// # Returns
    ///
    /// What became of it, once known; the sender drops when the binary does.
    pub fn commit(
        &mut self,
        shown: Shown,
        author: Author,
        cx: &mut Context<'_, Self>,
    ) -> oneshot::Receiver<Committed> {
        let (said, heard) = oneshot::channel();
        let first = shown.said().first().map_or("", String::as_str);
        let label = format!(
            "Editing: {}",
            first.chars().take(LABEL_MAX).collect::<String>()
        );
        let refused = match (&self.loaded, &self.editing) {
            (None, _) => Some(Committed::Refused("open a binary first".to_owned())),
            (_, Some(running)) => Some(Committed::Busy(format!(
                "{running} still runs; do it again once it ends"
            ))),
            (Some(_), None) => None,
        };
        if let Some(refused) = refused {
            if let Committed::Busy(why) | Committed::Refused(why) = &refused {
                self.set_status(format!("{label} refused: {why}"), cx);
            }
            drop(said.send(refused));
            return heard;
        }
        self.run(
            label,
            move |loaded| commit_blocking(loaded, shown),
            move |binary, base, out, cx| {
                let committed = binary.committed(&base, out, author, cx);
                drop(said.send(committed));
            },
            cx,
        );
        heard
    }

    /// Shows the state a commit left and keeps its entry, or says why the engine refused it.
    ///
    /// # Arguments
    ///
    /// * `base` - The state the commit ran over.
    /// * `out` - What [`commit_blocking`] returned.
    /// * `author` - Who made it.
    /// * `cx` - Binary context.
    ///
    /// # Returns
    ///
    /// What became of the commit.
    fn committed(
        &mut self,
        base: &Arc<LoadedBinary>,
        out: anyhow::Result<(Arc<LoadedBinary>, Shown)>,
        author: Author,
        cx: &mut Context<'_, Self>,
    ) -> Committed {
        match out {
            Ok((next, step)) => {
                let fingerprint = next.fingerprint;
                if !self.advance(base, next, cx) {
                    return Committed::Stale;
                }
                let mut said = text::visible(&step.receipt()).into_owned();
                if self
                    .history
                    .committed(author, step, fingerprint, Kind::Edit)
                {
                    said.push_str(&format!(
                        "; the oldest edits can no longer be undone: at most {STEPS_MAX} edits and about {} MiB of them are kept",
                        BYTES_MAX >> 20
                    ));
                }
                self.set_status(said, cx);
                Committed::Done
            }
            Err(err) => {
                let why = format!("{err:#}");
                self.set_status(format!("edit refused: {}", text::visible(&why)), cx);
                if err.is::<edit::Stale>() {
                    Committed::Stale
                } else {
                    Committed::Refused(why)
                }
            }
        }
    }

    /// Takes back the newest edit that can still be taken back, the person's or a model's
    /// the person accepted, or puts back the newest taken back, through the engine's revert
    /// in the background; an edit another one has since changed is passed over, and the
    /// status line says whose edit it was and what the step did, or the engine's reason
    /// none could be.
    ///
    /// # Arguments
    ///
    /// * `way` - Undo or redo.
    /// * `cx` - Binary context.
    pub fn step(&mut self, way: Way, cx: &mut Context<'_, Self>) {
        let tried = self.history.candidates(way);
        if tried.is_empty() {
            let none = match way {
                Way::Undo => "nothing to undo",
                Way::Redo => "nothing to redo",
            };
            self.set_status(none.to_owned(), cx);
            return;
        }
        self.run(
            way.name().to_owned(),
            move |loaded| step_blocking(loaded, &tried),
            move |binary, base, out, cx| match out {
                Ok((next, step, of)) => {
                    let fingerprint = next.fingerprint;
                    if binary.advance(&base, next, cx) {
                        let whose = binary
                            .history
                            .author_of(of)
                            .map_or_else(String::new, |a| format!("{} ", whose(&a)));
                        let said = format!(
                            "{}: {whose}edit: {}",
                            way.name(),
                            text::visible(&step.receipt())
                        );
                        binary
                            .history
                            .committed(Author::Person, step, fingerprint, way.kind(of));
                        binary.set_status(said, cx);
                    }
                }
                Err(why) => {
                    let why = text::visible(&why);
                    binary.set_status(format!("{} refused: {why}", way.name()), cx);
                }
            },
            cx,
        );
    }

    /// Returns the edits committed since the binary opened, oldest first, each with who
    /// made it and what it wrote: the change feed, whose entries Undo reads too.
    #[must_use]
    pub fn changes(&self) -> &[Entry] {
        self.history.entries()
    }
}
