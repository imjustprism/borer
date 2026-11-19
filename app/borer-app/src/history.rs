//! The change log of a window's binary.
//!
//! One entry per committed plan, with who made it and what it wrote: the change feed shows
//! the entries, and Undo and Redo take them back and put them again through the engine's
//! revert, so a step is checked as any edit is.

use std::sync::Arc;

use borer_engine::analysis::edit::Author;

use crate::worker::{LoadedBinary, Shown, commit_blocking, revert_blocking};

/// How many entries the log keeps; past it the oldest is dropped.
pub const STEPS_MAX: usize = 1000;

/// Most bytes the kept entries hold together, their lines and their changes' old and new
/// values ([`Shown::bytes`]); past it the oldest are dropped, the newest always kept.
pub const BYTES_MAX: usize = 64 << 20;

/// Which way a step moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Way {
    /// Takes the newest edit that can still be taken back.
    Undo,
    /// Puts back the newest edit taken back.
    Redo,
}

impl Way {
    /// Returns what the step is called in the job list and on the status line.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Undo => "Undo",
            Self::Redo => "Redo",
        }
    }

    /// Returns the kind of the entry a step of this way leaves, having moved entry `of`.
    ///
    /// # Arguments
    ///
    /// * `of` - The id of the entry the step took back or put again.
    #[must_use]
    pub const fn kind(self, of: u64) -> Kind {
        match self {
            Self::Undo => Kind::TakeBack { of },
            Self::Redo => Kind::Redo { of },
        }
    }
}

/// What an entry of the log did.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A plan its author committed.
    Edit,
    /// An undo: took back the entry `of`.
    TakeBack {
        /// The id of the entry taken back.
        of: u64,
    },
    /// A redo: took back the undo `of`, putting its edit again.
    Redo {
        /// The id of the undo taken back.
        of: u64,
    },
}

/// One committed plan: who made it, what it wrote and said, and the state it left.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    /// Its id, unique in the binary's log.
    pub id: u64,
    /// Who made it.
    pub author: Author,
    /// The plan and its lines, as shown and as committed, shared with the steps that try it.
    pub step: Arc<Shown>,
    /// How many bytes it holds ([`Shown::bytes`]), counted once when it was logged.
    pub bytes: usize,
    /// [`LoadedBinary::fingerprint`] of the overlay it left.
    pub fingerprint: u64,
    /// What it did.
    pub kind: Kind,
    /// Whether a later step took it back.
    pub taken_back: bool,
}

/// Returns how the status line names an author's edit: `your`, or the model's.
///
/// # Arguments
///
/// * `author` - Who made it.
#[must_use]
pub fn whose(author: &Author) -> String {
    match author {
        Author::Person => "your".to_owned(),
        Author::Model { provider, model } => format!("{provider} {model}'s"),
    }
}

/// The binary's log of committed plans, oldest first.
#[derive(Debug)]
pub struct History {
    /// The entries, oldest first, at most [`STEPS_MAX`].
    entries: Vec<Entry>,
    /// The id the next entry takes.
    next: u64,
    /// How many bytes the entries hold together.
    held: usize,
    /// Most bytes the entries hold together, [`BYTES_MAX`] but in tests.
    cap: usize,
}

impl Default for History {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            next: 0,
            held: 0,
            cap: BYTES_MAX,
        }
    }
}

impl History {
    /// Keeps `step`, a plan `author` just committed leaving the overlay `fingerprint`, as an
    /// entry of `kind`; an undo or a redo marks the entry it moved as taken back.
    ///
    /// # Arguments
    ///
    /// * `author` - Who made it.
    /// * `step` - The plan committed.
    /// * `fingerprint` - The overlay it left.
    /// * `kind` - What it did.
    ///
    /// # Returns
    ///
    /// Whether the oldest entries were dropped to keep [`STEPS_MAX`] and the byte cap.
    pub fn committed(&mut self, author: Author, step: Shown, fingerprint: u64, kind: Kind) -> bool {
        if let Kind::TakeBack { of } | Kind::Redo { of } = kind
            && let Some(moved) = self.entries.iter_mut().find(|e| e.id == of)
        {
            moved.taken_back = true;
        }
        let bytes = step.bytes();
        self.held = self.held.saturating_add(bytes);
        self.entries.push(Entry {
            id: self.next,
            author,
            step: Arc::new(step),
            bytes,
            fingerprint,
            kind,
            taken_back: false,
        });
        self.next = self.next.saturating_add(1);
        self.fit()
    }

    /// Returns the entries, oldest first.
    #[must_use]
    pub fn entries(&self) -> &[Entry] {
        &self.entries
    }

    /// Returns who made the entry `id`, `None` once it was dropped.
    ///
    /// # Arguments
    ///
    /// * `id` - The entry's id.
    #[must_use]
    pub fn author_of(&self, id: u64) -> Option<Author> {
        let entry = self.entries.iter().find(|e| e.id == id)?;
        let moved = match entry.kind {
            Kind::Edit => return Some(entry.author.clone()),
            Kind::TakeBack { of } | Kind::Redo { of } => of,
        };
        self.author_of(moved).or_else(|| Some(entry.author.clone()))
    }

    /// Returns the entries the next step `way` may move, newest first, each with its plan:
    /// for Undo every edit or redo not taken back; for Redo every undo not taken back since
    /// the newest edit, taken back or not, so an edit after an undo ends what Redo offers.
    ///
    /// # Arguments
    ///
    /// * `way` - Which way.
    #[must_use]
    pub fn candidates(&self, way: Way) -> Vec<(u64, Arc<Shown>)> {
        let newest = self.entries.iter().rev();
        let picked: Vec<&Entry> = match way {
            Way::Undo => newest
                .filter(|e| !e.taken_back && matches!(e.kind, Kind::Edit | Kind::Redo { .. }))
                .collect(),
            Way::Redo => newest
                .take_while(|e| e.kind != Kind::Edit)
                .filter(|e| !e.taken_back && matches!(e.kind, Kind::TakeBack { .. }))
                .collect(),
        };
        picked
            .into_iter()
            .map(|e| (e.id, Arc::clone(&e.step)))
            .collect()
    }

    /// Returns how many bytes the entries hold ([`Shown::bytes`]).
    #[must_use]
    pub const fn bytes(&self) -> usize {
        self.held
    }

    /// Drops the oldest entries until the log holds at most [`STEPS_MAX`] and its byte cap,
    /// keeping the newest.
    ///
    /// # Returns
    ///
    /// Whether any was dropped.
    fn fit(&mut self) -> bool {
        let mut dropped = 0;
        while self.entries.len() - dropped > 1
            && (self.entries.len() - dropped > STEPS_MAX || self.held > self.cap)
        {
            let oldest = self.entries.get(dropped).map_or(0, |e| e.bytes);
            self.held = self.held.saturating_sub(oldest);
            dropped += 1;
        }
        self.entries.drain(..dropped);
        dropped > 0
    }

    /// Forgets the newest entry, as if it had never been logged.
    #[cfg(test)]
    pub(crate) fn forget_newest(&mut self) {
        let forgot = self.entries.pop();
        self.held = self.held.saturating_sub(forgot.map_or(0, |e| e.bytes));
    }

    /// Forgets every entry, for a binary or a project put in place of the overlay.
    ///
    /// # Returns
    ///
    /// Whether any entry was forgotten.
    pub fn clear(&mut self) -> bool {
        let held = !self.entries.is_empty();
        self.entries.clear();
        self.held = 0;
        held
    }
}

/// Takes back the first entry of `tried` the engine lets be taken back over `loaded`.
///
/// It plans taking its changes back and commits that plan, its lines the step's receipt;
/// an entry a later edit has changed is passed over.
///
/// Must be called inside [`crate::worker::spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - The state now.
/// * `tried` - The entries to try, newest first, each with its plan.
///
/// # Returns
///
/// The state the step leaves, the plan that took the changes back, and the id of the entry
/// it moved.
///
/// # Errors
///
/// Returns the engine's refusal of the newest entry, in its words, when none can be taken
/// back; nothing was written.
pub fn step_blocking(
    loaded: &LoadedBinary,
    tried: &[(u64, Arc<Shown>)],
) -> Result<(Arc<LoadedBinary>, Shown, u64), String> {
    let mut first = None;
    for (id, step) in tried {
        match revert_blocking(loaded, step.changes()) {
            Ok(plan) => {
                let (next, step) =
                    commit_blocking(loaded, Shown::new(plan)).map_err(|e| format!("{e:#}"))?;
                return Ok((next, step, *id));
            }
            Err(why) => {
                first.get_or_insert(why);
            }
        }
    }
    Err(first.unwrap_or_else(|| "nothing to take back".to_owned()))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use borer_engine::analysis::edit::{Author, Change, Edit, Force};

    use super::{History, Kind, STEPS_MAX, Way};
    use crate::app_view::tests::loaded_of;
    use crate::code_view::tests::three_functions;
    use crate::worker::{Shown, planned_blocking};

    /// Returns a shown plan of `edits` over the three-function fixture.
    fn shown(edits: &[Edit]) -> Shown {
        let (program, analysis, overlay) = three_functions();
        let loaded = loaded_of(program, analysis, overlay);
        Shown::new(planned_blocking(&loaded, edits, Force::Refuse).unwrap().0)
    }

    /// Entries of a large declaration, committed, undone and put again over and over, keep
    /// the log within its byte cap counting each entry's changes, not only its lines, and
    /// keep the newest.
    #[test]
    fn entries_count_their_changes_against_the_byte_cap() {
        let text: String = (0..200)
            .map(|i| format!("struct S{i} {{ int a; int b; char name[32]; }};\n"))
            .collect();
        let step = shown(&[Edit::Declare { text }]);
        let changes: usize = step.changes().iter().map(Change::bytes).sum();
        let lines: usize = step.said().iter().map(String::len).sum();
        assert_eq!(step.bytes(), lines + changes);
        assert!(changes > 0);
        let mut history = History {
            cap: step.bytes() * 5 / 2,
            ..History::default()
        };
        for _ in 0..10 {
            history.committed(Author::Person, step.clone(), 1, Kind::Edit);
            let undone = history.candidates(Way::Undo)[0].0;
            history.committed(
                Author::Person,
                step.clone(),
                2,
                Kind::TakeBack { of: undone },
            );
            let redone = history.candidates(Way::Redo)[0].0;
            history.committed(Author::Person, step.clone(), 3, Kind::Redo { of: redone });
            assert!(history.bytes() <= history.cap, "{}", history.bytes());
            assert!(history.entries.len() <= 2);
        }
        assert!(!history.candidates(Way::Undo).is_empty());
    }

    /// Past [`STEPS_MAX`] entries the oldest is dropped and the newest kept.
    #[test]
    fn entries_past_the_count_cap_drop_the_oldest() {
        let step = shown(&[Edit::Name {
            at: 0x1000,
            name: "named".to_owned(),
        }]);
        let mut history = History::default();
        let dropped: Vec<bool> = (0..=STEPS_MAX)
            .map(|_| history.committed(Author::Person, step.clone(), 0, Kind::Edit))
            .collect();
        assert_eq!(dropped.iter().filter(|d| **d).count(), 1);
        assert_eq!(history.entries.len(), STEPS_MAX);
    }

    /// Undo and Redo offer the entries they may move.
    ///
    /// Undo offers every edit not taken back, newest first, a model's as well as the
    /// person's; Redo offers the undos since the last edit, and an edit after an undo ends
    /// what Redo offers; the author of an undo is the author of what it took back.
    #[test]
    fn undo_and_redo_offer_the_entries_they_may_move() {
        let step = shown(&[Edit::Name {
            at: 0x1000,
            name: "named".to_owned(),
        }]);
        let model = Author::Model {
            provider: "Fake".to_owned(),
            model: "fake".to_owned(),
        };
        let mut history = History::default();
        history.committed(Author::Person, step.clone(), 0, Kind::Edit);
        history.committed(model.clone(), step.clone(), 0, Kind::Edit);
        let ids =
            |h: &History, way| -> Vec<u64> { h.candidates(way).into_iter().map(|c| c.0).collect() };
        assert_eq!(ids(&history, Way::Undo), [1, 0]);
        assert!(ids(&history, Way::Redo).is_empty());
        history.committed(Author::Person, step.clone(), 0, Kind::TakeBack { of: 1 });
        assert_eq!(history.author_of(2), Some(model));
        assert_eq!(ids(&history, Way::Undo), [0]);
        assert_eq!(ids(&history, Way::Redo), [2]);
        history.committed(Author::Person, step, 0, Kind::Edit);
        assert!(ids(&history, Way::Redo).is_empty());
    }

    /// Redo offers nothing an edit came after, even an edit since taken back: after an edit,
    /// its undo, a second edit and its undo, Redo offers the second undo alone.
    #[test]
    fn redo_offers_only_the_undos_since_the_newest_edit() {
        let step = shown(&[Edit::Name {
            at: 0x1000,
            name: "named".to_owned(),
        }]);
        let mut history = History::default();
        history.committed(Author::Person, step.clone(), 0, Kind::Edit);
        history.committed(Author::Person, step.clone(), 0, Kind::TakeBack { of: 0 });
        history.committed(Author::Person, step.clone(), 0, Kind::Edit);
        history.committed(Author::Person, step, 0, Kind::TakeBack { of: 2 });
        let redo: Vec<u64> = history
            .candidates(Way::Redo)
            .into_iter()
            .map(|c| c.0)
            .collect();
        assert_eq!(redo, [3]);
    }
}
