//! A caller's request that the work running for it stop.
//!
//! The engine answers the same bytes for the same question, and nothing in
//! it reads the clock. A server still has to answer within a time its
//! client waits, so it hands the engine a [`Cancel`] it raises when that
//! time has passed. While the flag is in force ([`Cancel::within`]) every
//! emulator checks it every [`crate::emulate::CANCEL_EVERY`] steps and,
//! raised, stops at that step boundary with [`crate::emulate::Limit::Time`];
//! the decompile pipeline checks it at its passes and fixpoint rounds and,
//! raised, answers one line saying it stopped; and the sweeps over callers
//! and decoders take no further item. The flag is the one input that is
//! not the question, so a result built after it was raised is not memoized
//! ([`crate::analysis::Derived`]) nor stored ([`Cancel::whole`]): the next
//! request builds it whole, and a flag never raised changes no answer.
//!
//! The flag in force is per thread, the way the read-set frames are
//! ([`crate::analysis::reads`]), and every thread the engine spawns takes
//! both along ([`crate::analysis::reads::Handle`]).

use std::cell::RefCell;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

thread_local! {
    /// The flag in force on this thread, innermost [`Cancel::within`] last.
    static IN_FORCE: RefCell<Option<Cancel>> = const { RefCell::new(None) };
}

/// A flag a caller raises to stop the work running under it.
#[derive(Debug, Clone, Default)]
pub struct Cancel(Arc<AtomicBool>);

impl Cancel {
    /// Makes a flag not yet raised.
    ///
    /// # Returns
    ///
    /// The flag; clones share it.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Raises the flag.
    pub fn raise(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    /// Whether the flag was raised.
    ///
    /// # Returns
    ///
    /// `true` once [`Cancel::raise`] ran on it or a clone.
    #[must_use]
    pub fn is_raised(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }

    /// Runs `f` with this flag in force on this thread.
    ///
    /// # Arguments
    ///
    /// * `f` - The work the flag may stop.
    ///
    /// # Returns
    ///
    /// What `f` returns; the flag in force before is in force again after.
    pub fn within<R>(&self, f: impl FnOnce() -> R) -> R {
        let before = IN_FORCE.with(|c| c.replace(Some(self.clone())));
        let out = f();
        IN_FORCE.with(|c| *c.borrow_mut() = before);
        out
    }

    /// The flag in force on this thread.
    ///
    /// # Returns
    ///
    /// The flag, or `None` outside every [`Cancel::within`].
    #[must_use]
    pub(crate) fn current() -> Option<Self> {
        IN_FORCE.with(|c| c.borrow().clone())
    }

    /// Whether the flag in force on this thread was raised.
    ///
    /// # Returns
    ///
    /// `false` outside every [`Cancel::within`].
    #[must_use]
    pub fn raised() -> bool {
        IN_FORCE.with(|c| c.borrow().as_ref().is_some_and(Self::is_raised))
    }

    /// Hands back a result only when the flag in force was not raised
    /// while it was made, for a caller about to keep it past the request.
    ///
    /// # Arguments
    ///
    /// * `value` - The result, just made.
    ///
    /// # Returns
    ///
    /// The result, whole.
    ///
    /// # Errors
    ///
    /// When the flag in force was raised: the result may be partial, and
    /// the message says it was not kept.
    pub fn whole<T>(value: T) -> Result<T, String> {
        if Self::raised() {
            return Err(
                "the request's deadline passed before the result was whole, so it was not kept"
                    .to_owned(),
            );
        }
        Ok(value)
    }

    /// Runs `f` under a flag taken from another thread, or under none.
    ///
    /// # Arguments
    ///
    /// * `flag` - The flag [`Cancel::current`] read there.
    /// * `f` - The work.
    ///
    /// # Returns
    ///
    /// What `f` returns.
    pub(crate) fn carried<R>(flag: Option<&Self>, f: impl FnOnce() -> R) -> R {
        match flag {
            Some(flag) => flag.within(f),
            None => f(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Cancel;

    /// A flag is in force only inside `within`, and nested ones restore
    /// the outer one.
    ///
    /// # Panics
    ///
    /// When a flag leaks out of its scope or a raise is not seen.
    #[test]
    fn a_flag_is_in_force_only_within() {
        assert!(Cancel::current().is_none());
        let outer = Cancel::new();
        let inner = Cancel::new();
        inner.raise();
        outer.within(|| {
            assert!(!Cancel::raised());
            inner.within(|| assert!(Cancel::raised()));
            assert!(!Cancel::raised());
        });
        assert!(Cancel::current().is_none());
    }
}
