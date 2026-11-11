//! Tests of the pool the sweeps over functions run on ([`striped_on`]), at
//! thread counts the tests choose: the order of its results, and what a
//! panic on one item costs.

use std::panic::{AssertUnwindSafe, catch_unwind};

use super::{Derived, striped_on};

/// Maps 300 items on `threads` threads, each item to itself, with `bad`
/// panicking.
///
/// # Arguments
///
/// * `threads` - How many threads.
/// * `bad` - The item that panics; one past the items panics nowhere.
///
/// # Panics
///
/// On the item `bad`.
fn mapped(threads: usize, bad: usize) -> Vec<usize> {
    let items: Vec<usize> = (0..300).collect();
    striped_on(
        threads,
        &items,
        || (),
        |(), &x| {
            assert_ne!(x, bad, "item {bad} does not map");
            x
        },
    )
}

/// Results come back in the items' order at every thread count, each
/// worker over a state of its own.
///
/// # Panics
///
/// When a result is out of place or missing.
#[test]
fn results_keep_the_items_order_at_any_thread_count() {
    let items: Vec<usize> = (0..300).collect();
    let want: Vec<usize> = items.iter().map(|x| x * 2 + 7).collect();
    for threads in [0, 1, 2, 7, 8, 299, 300, 1000] {
        let got = striped_on(threads, &items, || 7, |seven, x| x * 2 + seven);
        assert_eq!(got, want, "{threads} threads");
    }
    assert_eq!(striped_on(8, &[], || (), |(), x: &usize| *x), []);
}

/// A panic on one item fails the whole call with the item's own message,
/// on one thread and on eight alike.
///
/// A worker that panicked was once left out of the results: every eighth
/// item came back as nothing found, where the same map on one thread
/// raised.
///
/// # Panics
///
/// When a call returns, or fails with another message.
#[test]
fn a_panic_on_one_item_fails_the_call_at_any_thread_count() {
    for threads in [1, 8] {
        let failed = catch_unwind(|| mapped(threads, 123)).expect_err("the panic reaches us");
        let message = failed.downcast::<String>().expect("the item's message");
        assert!(message.contains("item 123 does not map"), "{message}");
    }
}

/// A result built across the cores is not kept when one item panics: the
/// next request builds it whole.
///
/// # Panics
///
/// When the panic stays inside the build, or a later build finds a result
/// already there.
#[test]
fn a_build_whose_worker_panics_keeps_nothing() {
    let derived = Derived::default();
    let count = |bad: usize| derived.get_or_build("mapped", (), || mapped(8, bad).len());
    let failed = catch_unwind(AssertUnwindSafe(|| count(123)));
    assert!(failed.is_err(), "the panic reaches the request");
    assert_eq!(*count(300), 300, "the build that panicked left a result");
}
