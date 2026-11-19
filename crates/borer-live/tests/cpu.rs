//! The processor time a process has spent ([`borer_live::process_cpu_ticks`]),
//! in a test binary of its own, so no other test spends processor time in
//! the process while it reads.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_live::process_cpu_ticks;

/// Turns of the spin loop each measured piece of work runs.
const TURNS: u64 = 50_000_000;

/// Spins `turns` times.
///
/// # Arguments
///
/// * `turns` - How many times to turn the loop.
fn spin(turns: u64) {
    for i in 0..turns {
        std::hint::black_box(i);
    }
}

/// Work done on a thread that has ended counts as the same work done on
/// the reading thread, and twice the work counts about twice the time.
///
/// The reading thread only waits while the other spins, so a count that
/// left out ended threads would read near nothing for it.
#[test]
fn an_ended_thread_counts_by_its_work() {
    let spent = |work: &dyn Fn()| {
        let before = process_cpu_ticks().expect("processor time");
        work();
        process_cpu_ticks()
            .expect("processor time")
            .saturating_sub(before)
    };
    let on_a_thread = |turns: u64| {
        std::thread::spawn(move || spin(turns))
            .join()
            .expect("the spinning thread");
    };
    let here = spent(&|| spin(TURNS));
    let there = spent(&|| on_a_thread(TURNS));
    let twice = spent(&|| on_a_thread(TURNS * 2));
    assert!(
        there > here / 2 && there < here * 2,
        "the same work read {there} on an ended thread and {here} here"
    );
    assert!(
        twice > there * 3 / 2 && twice < there * 3,
        "twice the work read {twice} against {there}"
    );
}
