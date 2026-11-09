//! Where a run went: the landings a profile counts, and which of the block
//! starts it was watched for it executed.

use super::Emulator;

impl Emulator<'_> {
    /// Notes the instruction at `ip` as the run is about to execute it: a
    /// landing a profile counts, and a watched block start reached.
    ///
    /// # Arguments
    ///
    /// * `ip` - The instruction's address.
    pub(super) fn note_step(&mut self, ip: u64) {
        if self.profiling && ip != self.fall_through {
            *self.hits.entry(ip).or_insert(0) += 1;
        }
        if let Ok(k) = self.watched.binary_search_by_key(&ip, |w| w.0)
            && let Some(w) = self.watched.get_mut(k)
        {
            w.1 = true;
        }
    }

    /// Watches the runs that follow for the block starts given, so
    /// [`Emulator::reached`] can say which of them executed: how far a
    /// function's inputs took it.
    ///
    /// # Arguments
    ///
    /// * `starts` - The blocks' first instruction addresses, any order.
    pub fn watch_starts(&mut self, starts: impl IntoIterator<Item = u64>) {
        let mut watched: Vec<(u64, bool)> = starts.into_iter().map(|s| (s, false)).collect();
        watched.sort_unstable();
        watched.dedup();
        self.watched = watched;
    }

    /// The watched block starts a run executed, in address order.
    #[must_use]
    pub fn reached(&self) -> Vec<u64> {
        self.watched.iter().filter(|w| w.1).map(|w| w.0).collect()
    }
}
