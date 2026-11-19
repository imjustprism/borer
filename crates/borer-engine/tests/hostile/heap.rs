//! The heap counter the bars on a load's heap read ([`measured`]), and
//! the lock ([`serial`]) every test in this binary holds so that no other
//! test's allocations land in a measured window.

use std::alloc::{GlobalAlloc, Layout, System};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use borer_engine::program::read_regular;

/// Live heap bytes, kept by [`Counting`].
static LIVE: AtomicUsize = AtomicUsize::new(0);
/// Highest [`LIVE`] since the last [`measured`] began.
static PEAK: AtomicUsize = AtomicUsize::new(0);
/// One test at a time, since the counters are process-wide: every test in
/// this binary holds it, or what it allocates on its own thread is charged
/// to a load measured on another.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The system allocator with a live-bytes counter and a high-water mark.
struct Counting;

/// Adds `n` live bytes and raises the peak.
fn bump(n: usize) {
    let now = LIVE.fetch_add(n, Ordering::Relaxed) + n;
    PEAK.fetch_max(now, Ordering::Relaxed);
}

#[expect(
    unsafe_code,
    reason = "a global allocator is the one way to measure what a load allocates"
)]
// SAFETY: every method forwards to `System` unchanged and only counts bytes.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's `alloc` contract is passed on unchanged.
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            bump(layout.size());
        }
        p
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller's `alloc_zeroed` contract is passed on unchanged.
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            bump(layout.size());
        }
        p
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` came from `System` through this allocator with `layout`.
        unsafe { System.dealloc(ptr, layout) };
        LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: `ptr` came from `System` through this allocator with `layout`.
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if !p.is_null() {
            LIVE.fetch_sub(layout.size(), Ordering::Relaxed);
            bump(new_size);
        }
        p
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// Runs `f` and reports the most heap it held beyond what was live before.
///
/// # Arguments
///
/// * `f` - The work to measure.
///
/// # Returns
///
/// The result and the extra bytes at the peak.
pub(crate) fn measured<T>(f: impl FnOnce() -> T) -> (T, usize) {
    let before = LIVE.load(Ordering::Relaxed);
    PEAK.store(before, Ordering::Relaxed);
    let out = f();
    (out, PEAK.load(Ordering::Relaxed).saturating_sub(before))
}

/// Runs `f` and reports the heap it left held.
///
/// # Arguments
///
/// * `f` - The work to measure.
///
/// # Returns
///
/// The result and the live bytes after `f` beyond those before.
pub(crate) fn kept<T>(f: impl FnOnce() -> T) -> (T, usize) {
    let before = LIVE.load(Ordering::Relaxed);
    let out = f();
    (out, LIVE.load(Ordering::Relaxed).saturating_sub(before))
}

/// Takes the serial lock, poisoned or not.
pub(crate) fn serial() -> std::sync::MutexGuard<'static, ()> {
    SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Every test in this binary, its submodules' too, holds [`serial`].
///
/// A test that did not take it allocated on its own thread while another
/// measured a load, and under a full gate's load the 2048-byte file of
/// `a_section_whose_sizes_cannot_be_true_is_not_mapped` seemed to hold
/// 412296 bytes beyond itself. The submodules are the `#[path]` lines of
/// `hostile.rs`.
#[test]
fn every_test_here_holds_the_serial_lock() {
    let _serial = serial();
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests");
    let read = |file: &str| {
        let bytes = read_regular(&dir.join(file), u64::MAX).expect("a test source reads");
        String::from_utf8(bytes).expect("a test source is UTF-8")
    };
    let root = read("hostile.rs");
    let modules = root
        .lines()
        .filter_map(|line| line.strip_prefix("#[path = \"")?.strip_suffix("\"]"));
    let mut open = Vec::new();
    for file in std::iter::once("hostile.rs").chain(modules) {
        let text = read(file);
        let lines: Vec<&str> = text.lines().collect();
        for (at, _) in lines
            .iter()
            .enumerate()
            .filter(|(_, l)| l.trim() == "#[test]")
        {
            let mut body = lines[at..].iter().take_while(|l| **l != "}");
            if !body.clone().any(|l| l.contains("serial()")) {
                let name = body.find(|l| l.starts_with("fn ")).unwrap_or(&"?");
                open.push(format!("{file}: {name}"));
            }
        }
    }
    assert!(open.is_empty(), "tests without the serial lock: {open:#?}");
}
