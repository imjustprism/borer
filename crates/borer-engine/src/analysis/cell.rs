//! One result's cell in [`super::Derived`]: the thread that builds it, the
//! result it hands the threads that waited, and what the result weighs.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize};
use std::sync::{Arc, OnceLock};

use super::reads;

/// One result's cell in [`super::Derived`].
pub(super) struct Cell<T> {
    /// Taken by the one thread that builds the result; every other thread
    /// asking for it waits for [`Cell::value`].
    pub(super) claimed: AtomicBool,
    /// The result, once built, and what its build read of the overlay
    /// ([`Shared`]).
    pub(super) value: OnceLock<Shared<T>>,
    /// Bytes an item's result holds, set before the result is.
    pub(super) weight: AtomicUsize,
    /// [`super::Derived`]'s ask count when an item's result was last asked
    /// for.
    pub(super) asked: AtomicU64,
}

impl<T> Default for Cell<T> {
    fn default() -> Self {
        Self {
            claimed: AtomicBool::new(false),
            value: OnceLock::new(),
            weight: AtomicUsize::new(0),
            asked: AtomicU64::new(0),
        }
    }
}

/// What a build hands the threads waiting on its cell: the result and what
/// its build read of the overlay, or `None` when it left nothing to share.
///
/// That is a build that ended after its caller's cancel flag was raised
/// ([`crate::cancel::Cancel`]), so an emulation in it may have been cut
/// short, or one that unwound; such a cell is let go at once.
pub(super) type Shared<T> = Option<(Arc<T>, reads::Reads)>;

/// Hands a build's result to the threads waiting on its cell when dropped.
///
/// It hands what the build filled in, else nothing, so a build cut short or
/// unwound still lets them go on, each to build its own.
pub(super) struct Publish<'a, T>(pub(super) &'a OnceLock<Shared<T>>, pub(super) Shared<T>);

impl<T> Drop for Publish<'_, T> {
    fn drop(&mut self) {
        self.0.get_or_init(|| self.1.take());
    }
}
