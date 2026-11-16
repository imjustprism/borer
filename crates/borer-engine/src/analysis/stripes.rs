//! The pool the sweeps over functions run on: a map striped across the
//! cores, results in the items' order, and two passes run side by side.

use super::reads;

/// Fewest functions worth spreading over the cores in a sweep.
const STRIPE_MIN: usize = 256;

/// Maps `f` over `items` across the cores, results in the items' order.
///
/// Workers take every `threads`-th item, so the work spreads without a
/// queue. With one core, or fewer than 256 items, the map runs inline. A
/// panic in `f` fails the call either way ([`striped_on`]).
///
/// # Arguments
///
/// * `items` - The inputs.
/// * `f` - The per-item function; it sees only shared references.
///
/// # Returns
///
/// One result per item, in order.
pub(crate) fn striped<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    striped_with(items, STRIPE_MIN, || (), |(), x| f(x))
}

/// Maps `f` over `items` across the cores with a state per worker (a
/// context carrying memos), results in the items' order.
///
/// The cores are those [`crate::progress::cores`] allows. Workers take
/// every `threads`-th item; each makes its own state with
/// `init` first, so a memo need not be shared. With one core, or fewer
/// than `min` items, the map runs inline over one state. A panic in `f`
/// fails the call either way ([`striped_on`]).
///
/// # Arguments
///
/// * `items` - The inputs.
/// * `min` - Fewest items worth a thread each.
/// * `init` - Makes one worker's state.
/// * `f` - The per-item function over the worker's state.
///
/// # Returns
///
/// One result per item, in order.
pub(crate) fn striped_with<T: Sync, S, R: Send>(
    items: &[T],
    min: usize,
    init: impl Fn() -> S + Sync,
    f: impl Fn(&S, &T) -> R + Sync,
) -> Vec<R> {
    let threads = if items.len() < min {
        1
    } else {
        crate::progress::cores()
    };
    striped_on(threads, items, init, f)
}

/// Maps `f` over `items` on up to `threads` threads with a state per
/// thread, results in the items' order: [`striped_with`] told how many
/// threads rather than reading the machine's.
///
/// A panic in `init` or `f` fails the whole call, at any thread count
/// ([`joined`]): no caller is handed results with a worker's share
/// missing, and no result built from them is kept ([`super::Derived`] lets go of a
/// build that unwinds).
///
/// # Arguments
///
/// * `threads` - Most threads to map on; with one, or one item, the map
///   runs inline.
/// * `items` - The inputs.
/// * `init` - Makes one worker's state.
/// * `f` - The per-item function over the worker's state.
///
/// # Returns
///
/// One result per item, in order.
pub(crate) fn striped_on<T: Sync, S, R: Send>(
    threads: usize,
    items: &[T],
    init: impl Fn() -> S + Sync,
    f: impl Fn(&S, &T) -> R + Sync,
) -> Vec<R> {
    let threads = threads.min(items.len());
    let sweep = crate::progress::Sweep::start(items.len());
    let counted = |state: &S, x: &T, tally: &mut crate::progress::Tally<'_>| {
        let out = f(state, x);
        tally.one();
        out
    };
    if threads <= 1 {
        let (state, mut tally) = (init(), sweep.tally());
        return items
            .iter()
            .map(|x| counted(&state, x, &mut tally))
            .collect();
    }
    let (init, counted, sweep) = (&init, &counted, &sweep);
    let here = reads::Handle::here();
    let mut stripes: Vec<std::vec::IntoIter<R>> = std::thread::scope(|scope| {
        let workers = (0..threads).map(|t| {
            let here = here.clone();
            scope.spawn(move || {
                here.enter(|| {
                    let (state, mut tally) = (init(), sweep.tally());
                    let stripe = items.iter().skip(t).step_by(threads);
                    stripe
                        .map(|x| counted(&state, x, &mut tally))
                        .collect::<Vec<_>>()
                })
            })
        });
        let stripes = joined(workers.collect());
        stripes.into_iter().map(Vec::into_iter).collect()
    });
    (0..items.len())
        .filter_map(|i| stripes.get_mut(i % threads)?.next())
        .collect()
}

/// Waits for a scope's workers in order and returns what each returned,
/// raising a worker's panic again on the calling thread.
///
/// A worker that panicked is never read as one that found nothing: its
/// panic ends the caller's work as it would have on one thread.
///
/// # Arguments
///
/// * `workers` - The workers.
///
/// # Returns
///
/// What the workers returned, in their order.
pub(crate) fn joined<T>(workers: Vec<std::thread::ScopedJoinHandle<'_, T>>) -> Vec<T> {
    let ended = workers.into_iter().map(std::thread::ScopedJoinHandle::join);
    ended
        .map(|worker| worker.unwrap_or_else(|panic| std::panic::resume_unwind(panic)))
        .collect()
}

/// Runs `side` on a thread of its own while `main` runs on this one.
///
/// For two passes that read nothing of each other: the analysis scans the
/// image for crypto tables, which reads the program alone, while discovery
/// walks the code. With one core both run here, `main` first.
///
/// # Arguments
///
/// * `main` - The pass this thread runs.
/// * `side` - The pass the other thread runs.
///
/// # Returns
///
/// What `main` returned, and what `side` returned or `None` when its
/// thread failed.
pub(crate) fn beside<M, S: Send>(
    main: impl FnOnce() -> M,
    side: impl FnOnce() -> S + Send,
) -> (M, Option<S>) {
    if crate::progress::cores() <= 1 {
        let m = main();
        return (m, Some(side()));
    }
    let here = reads::Handle::here();
    std::thread::scope(|scope| {
        let handle = scope.spawn(|| here.enter(side));
        let m = main();
        (m, handle.join().ok())
    })
}
