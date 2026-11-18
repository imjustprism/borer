//! Assert-shaped references in bulk: the assertion index reads them in
//! time linear in the references and in heap within the file-size bar.

use borer_engine::analysis::render::{asserted_fields_tsv, source_tree_tsv};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::{from_usize, lo32};
use borer_engine::program::{Arch, Program, Section};

use super::{LOAD_HEAP_PER_BYTE, measured, serial};

/// Where `.text` starts, and the function there.
const TEXT: u64 = 0x1000;

/// Builds an image whose one function references `targets` in order,
/// each by a `lea rcx,[rip+target]`, then returns.
///
/// `.text` sits at [`TEXT`], entered there, and the read-only `rdata`
/// after it, page-aligned; `targets` are offsets into `rdata`.
///
/// # Arguments
///
/// * `rdata` - The read-only data.
/// * `targets` - The offsets into `rdata` the function references.
fn referencing(rdata: &[u8], targets: &[usize]) -> Program {
    let text_len = (7 * targets.len() + 1).next_multiple_of(0x1000);
    let rdata_va = TEXT + from_usize(text_len);
    let mut bytes = Vec::with_capacity(text_len + rdata.len());
    for (k, &target) in targets.iter().enumerate() {
        let end = TEXT + from_usize(7 * k + 7);
        bytes.extend_from_slice(&[0x48, 0x8d, 0x0d]); // ASM: lea rcx,[rip+target]
        let to = rdata_va + from_usize(target);
        bytes.extend_from_slice(&lo32(to.wrapping_sub(end)).to_le_bytes());
    }
    bytes.push(0xc3); // ASM: ret
    bytes.resize(text_len, 0xcc);
    let rdata_len = rdata.len().next_multiple_of(0x1000);
    bytes.extend_from_slice(rdata);
    bytes.resize(text_len + rdata_len, 0);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(TEXT),
        vec![
            Section::mapped(".text", TEXT, 0, from_usize(text_len), false, true),
            Section::mapped(
                ".rdata",
                rdata_va,
                from_usize(text_len),
                from_usize(rdata_len),
                false,
                false,
            ),
        ],
    )
}

/// The source path and the signature every assert-shaped site cites,
/// each terminated, back to back.
const CITED: &[u8] = b"src/h.cpp\0void H::f()\0";

/// Builds an image whose one function makes `n` assert-shaped references:
/// each a distinct bare condition (`!a00000`), then the path and the
/// signature of [`CITED`].
///
/// # Arguments
///
/// * `n` - How many sites.
fn asserting(n: usize) -> Program {
    let mut rdata = CITED.to_vec();
    let mut targets = Vec::with_capacity(3 * n);
    for k in 0..n {
        targets.extend([rdata.len(), 0, 10]);
        rdata.extend_from_slice(format!("!a{k:05}\0").as_bytes());
    }
    referencing(&rdata, &targets)
}

/// The assertion index over one function's many assert-shaped sites is
/// linear in them.
///
/// Each condition was checked against the function's whole list of
/// conditions, n²/2 comparisons with no cancel check: a function of a
/// million sites held a request for about ten minutes. Eight times the
/// sites now take about eight times the time, where the quadratic check
/// took sixty-four.
#[test]
fn many_assert_sites_in_one_function_read_in_linear_time() {
    /// Sites in the smaller function.
    const SITES: usize = 5000;
    let _serial = serial();
    let timed = |n: usize| {
        let p = asserting(n);
        let a = Analysis::compute(&p);
        #[expect(
            clippy::disallowed_methods,
            reason = "the test bounds the time a hostile image takes"
        )]
        let started = std::time::Instant::now();
        let text = asserted_fields_tsv(&p, &a, &Overlay::default(), "zzz");
        let took = started.elapsed();
        assert!(text.starts_with("# 0 of 0 asserted field names"), "{text}");
        took
    };
    let short = timed(SITES);
    let long = timed(8 * SITES);
    println!(
        "assert sites: {SITES} in {short:?}, {} in {long:?}",
        8 * SITES
    );
    assert!(
        long <= short * 16 + std::time::Duration::from_millis(100),
        "{} sites took {long:?}, {SITES} took {short:?}",
        8 * SITES
    );
}

/// The assertion index holds no text for the references that are no
/// assert's condition, within the file-size heap bar.
///
/// One function references a 1 MB run of printable bytes at a hundred
/// thousand places, beside one real assert: every reference's text, up to
/// a kilobyte each, was read and kept before the shape was checked.
#[test]
fn references_into_a_long_run_hold_no_text() {
    /// References into the run.
    const REFS: usize = 100_000;
    let _serial = serial();
    let mut rdata = CITED.to_vec();
    let cond = rdata.len();
    rdata.extend_from_slice(b"!m_x\0");
    let run = rdata.len();
    rdata.resize(run + (1 << 20), b'+');
    rdata.push(0);
    let mut targets = vec![cond, 0, 10];
    targets.extend((0..REFS).map(|k| run + 8 * k));
    let p = referencing(&rdata, &targets);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    source_tree_tsv(&p, &a, &o, "");
    let (text, extra) = measured(|| asserted_fields_tsv(&p, &a, &o, "zzz"));
    assert!(text.starts_with("# 0 of 0 asserted field names"), "{text}");
    let size = p.bytes.len();
    println!("assert index: {size} byte file, {extra} bytes of heap");
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * size,
        "a {size} byte file took {extra} bytes of heap to index its asserts"
    );
}
