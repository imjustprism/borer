//! The stack a decompile runs on: [`DECOMPILE_STACK`] bytes, on a thread
//! made for it or on a sweep's worker that has them already.

/// Stack bytes a decompile runs on: deep structure is not a fault, so the
/// thread is sized for [`super::MAX_DEPTH`] frames of a fat function.
const DECOMPILE_STACK: usize = 64 << 20;

thread_local! {
    /// Whether this thread was made with [`DECOMPILE_STACK`] bytes of stack
    /// (a sweep's [`worker`]) and runs no decompile now: one started on it
    /// then runs in place ([`roomy`]).
    static ROOMY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Runs a decompile with [`DECOMPILE_STACK`] bytes of stack: in place on a
/// thread that has that room and runs no decompile, else on a thread of its
/// own, which notes its reads into the caller's build.
///
/// PERF: a thread of its own for each function of a sweep cost a tenth of
/// a millisecond to make and join, so a sweep's workers lend theirs.
///
/// # Arguments
///
/// * `f` - The decompile.
///
/// # Returns
///
/// What `f` returned; `None` when it panicked, as a thread of its own
/// would have ended, or when no thread could be made.
#[cfg(not(target_arch = "wasm32"))]
pub(super) fn roomy<T: Send>(f: impl FnOnce() -> Option<T> + Send) -> Option<T> {
    if ROOMY.replace(false) {
        let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        ROOMY.set(true);
        return out.ok().flatten();
    }
    let here = crate::analysis::reads::Handle::here();
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(DECOMPILE_STACK)
            .spawn_scoped(scope, || here.enter(f))
            .ok()?
            .join()
            .ok()
            .flatten()
    })
}

/// Spawns a worker of a sweep on `scope` with [`DECOMPILE_STACK`] bytes of
/// stack, so the decompiles it runs stay on it ([`roomy`]).
///
/// # Arguments
///
/// * `scope` - The sweep's scope.
/// * `work` - What the worker does.
///
/// # Returns
///
/// The worker, or `None` when no thread could be made.
pub(super) fn worker<'scope, T: Send + 'scope>(
    scope: &'scope std::thread::Scope<'scope, '_>,
    work: impl FnOnce() -> T + Send + 'scope,
) -> Option<std::thread::ScopedJoinHandle<'scope, T>> {
    std::thread::Builder::new()
        .stack_size(DECOMPILE_STACK)
        .spawn_scoped(scope, move || {
            ROOMY.set(true);
            work()
        })
        .ok()
}
