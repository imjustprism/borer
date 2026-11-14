//! Back and forward function-entry history stack.

/// Tracks opened function entry addresses for back and forward navigation.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct NavHistory {
    /// Previously visited function entries, oldest to newest.
    back: Vec<u64>,
    /// Currently displayed function entry, if one is open.
    current: Option<u64>,
    /// Entries stepped back from, ready to revisit on [`Self::go_forward`].
    forward: Vec<u64>,
}

impl NavHistory {
    /// Creates an empty navigation history.
    ///
    /// # Returns
    ///
    /// Empty [`NavHistory`].
    #[must_use]
    pub const fn new() -> Self {
        Self {
            back: Vec::new(),
            current: None,
            forward: Vec::new(),
        }
    }

    /// Clears all back, current, and forward entries when a new binary loads.
    pub fn clear(&mut self) {
        self.back.clear();
        self.current = None;
        self.forward.clear();
    }

    /// Records opening `entry`, pushing the previous entry onto the back stack
    /// and clearing forward history when `entry` differs from [`Self::current`].
    ///
    /// # Arguments
    ///
    /// * `entry` - Virtual address of the newly opened function.
    ///
    /// # Returns
    ///
    /// `true` when [`Self::current`] changed, `false` when `entry` was already current.
    pub fn open(&mut self, entry: u64) -> bool {
        if self.current == Some(entry) {
            return false;
        }
        if let Some(prev) = self.current.replace(entry) {
            self.back.push(prev);
        }
        self.forward.clear();
        true
    }

    /// Steps back to the previously visited function entry.
    ///
    /// # Returns
    ///
    /// Newly current function entry, or `None` when the back stack is empty.
    pub fn go_back(&mut self) -> Option<u64> {
        let prev = self.back.pop()?;
        if let Some(cur) = self.current.replace(prev) {
            self.forward.push(cur);
        }
        Some(prev)
    }

    /// Steps forward to the function entry most recently stepped back from.
    ///
    /// # Returns
    ///
    /// Newly current function entry, or `None` when the forward stack is empty.
    pub fn go_forward(&mut self) -> Option<u64> {
        let next = self.forward.pop()?;
        if let Some(cur) = self.current.replace(next) {
            self.back.push(cur);
        }
        Some(next)
    }

    /// Returns the currently open function entry.
    ///
    /// # Returns
    ///
    /// Active function virtual address, or `None` if none has been opened.
    #[must_use]
    pub const fn current(&self) -> Option<u64> {
        self.current
    }

    /// Reports whether [`Self::go_back`] has at least one entry.
    #[must_use]
    pub fn can_go_back(&self) -> bool {
        !self.back.is_empty()
    }

    /// Reports whether [`Self::go_forward`] has at least one entry.
    #[must_use]
    pub fn can_go_forward(&self) -> bool {
        !self.forward.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::NavHistory;

    /// Back and forward walk a sequence of opens and clear forward on a fresh branch.
    ///
    /// # Panics
    ///
    /// Panics if back, forward, or branch truncation yields the wrong entry.
    #[test]
    fn back_and_forward_walk_open_sequence() {
        let mut hist = NavHistory::new();
        assert_eq!(hist.current(), None);
        assert_eq!(hist.go_back(), None);
        assert_eq!(hist.go_forward(), None);

        assert!(hist.open(0x1000));
        assert!(!hist.open(0x1000));
        assert!(hist.open(0x2000));
        assert!(hist.open(0x3000));
        assert_eq!(hist.current(), Some(0x3000));

        assert_eq!(hist.go_back(), Some(0x2000));
        assert_eq!(hist.go_back(), Some(0x1000));
        assert_eq!(hist.go_back(), None);
        assert_eq!(hist.current(), Some(0x1000));

        assert_eq!(hist.go_forward(), Some(0x2000));
        assert!(hist.open(0x4000));
        assert!(!hist.can_go_forward());
        assert_eq!(hist.go_forward(), None);
        assert_eq!(hist.go_back(), Some(0x2000));
        assert_eq!(hist.go_back(), Some(0x1000));
    }
}
