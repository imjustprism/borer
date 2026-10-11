//! Wall-clock phase marks behind `BORER_TIMING`, for profiling a load or
//! analysis without a profiler.
//!
//! The engine never prints: its outputs are answers. The one exception is
//! this knob, inert unless the environment variable is set, which writes
//! one stderr line per marked phase so the seconds of a big binary's first
//! answer can be split into their parts. Nothing it prints is part of any
//! answer, so determinism of output is untouched.

/// One stderr line per [`Phases::mark`], when `BORER_TIMING` is set.
///
/// Constructed once at the top of the pass being measured; each mark names
/// the phase that just ended and restarts the clock, so the lines sum to
/// the whole pass.
#[derive(Debug)]
pub(crate) struct Phases(Option<std::time::Instant>);

impl Phases {
    /// Starts the clock, or stays inert when timing is off.
    ///
    /// # Returns
    ///
    /// The mark holder for one pass.
    #[expect(
        clippy::disallowed_methods,
        reason = "wall time printed to stderr behind BORER_TIMING only, never an output"
    )]
    pub(crate) fn new() -> Self {
        /// Whether `BORER_TIMING` is set in the environment.
        static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        Self(
            ON.get_or_init(|| std::env::var_os("BORER_TIMING").is_some())
                .then(std::time::Instant::now),
        )
    }

    /// Prints the time since the last mark and restarts the clock.
    ///
    /// # Arguments
    ///
    /// * `name` - The phase that just ended.
    #[expect(
        clippy::disallowed_methods,
        reason = "wall time printed to stderr behind BORER_TIMING only, never an output"
    )]
    pub(crate) fn mark(&mut self, name: &str) {
        if let Some(t0) = self.0 {
            eprintln!("borer timing: {name} {:?}", t0.elapsed());
            self.0 = Some(std::time::Instant::now());
        }
    }
}

impl Default for Phases {
    /// A mark holder, timing still decided by the environment.
    fn default() -> Self {
        Self::new()
    }
}
