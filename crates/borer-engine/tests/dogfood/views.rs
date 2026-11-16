//! The view sweeps of the dogfood corpus: every function's text, listing,
//! linear listing and control-flow graph read as a view, each answering
//! what its code shows, the same on any thread count.

use super::{CORPUS, Corpus, drawn, view_sweep};
use borer_engine::analysis::decompile::view::view_of;
use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::program::Program;
use borer_engine::view::{Kind, Ref, Said};
use std::collections::{BTreeMap, BTreeSet};

/// Returns each function's text as the sweep rendered it, named where it
/// has a named one ([`Swept::named`], else [`Swept::text`]).
///
/// # Arguments
///
/// * `c` - The corpus.
fn swept_texts(c: &Corpus) -> Vec<(u64, &str)> {
    c.analysis
        .functions
        .iter()
        .zip(c.swept())
        .filter_map(|(f, s)| {
            let s = s.as_ref()?;
            Some((f.entry, s.named.as_deref().unwrap_or(&s.text)))
        })
        .collect()
}

/// Returns a hash of each text's view, on `threads` threads taking the
/// texts from one queue: a hash of every token's line, end, kind and link
/// in order, the view's canonical dump.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
/// * `texts` - Each function's entry and text.
/// * `threads` - How many threads read the views.
#[expect(
    clippy::expect_used,
    reason = "a worker thread that panics fails the sweep"
)]
fn view_dumps(p: &Program, a: &Analysis, texts: &[(u64, &str)], threads: usize) -> Vec<u64> {
    use std::hash::{DefaultHasher, Hash, Hasher};
    let next = std::sync::atomic::AtomicUsize::new(0);
    let dump = |entry: u64, text: &str| {
        let mut out = String::new();
        if let Some(v) = view_of(p, a, &Overlay::default(), entry, text) {
            for i in 0..v.lines() {
                for (span, kind, link) in v.tokens(i) {
                    out.push_str(&format!("{i}\t{}\t{kind:?}\t{link:?}\n", span.end));
                }
            }
        }
        let mut h = DefaultHasher::new();
        out.hash(&mut h);
        h.finish()
    };
    let mut each: Vec<(usize, u64)> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(&(entry, text)) = texts.get(k) else {
                            return done;
                        };
                        done.push((k, dump(entry, text)));
                    }
                })
            })
            .collect();
        workers
            .into_iter()
            .flat_map(|w| w.join().expect("a view thread"))
            .collect()
    });
    each.sort_unstable();
    each.into_iter().map(|(_, h)| h).collect()
}

/// Every function's view of the `BORER_DOGFOOD` binary reads the same
/// tokens on one thread and on every core, and again in one process.
///
/// The views read the sweep's texts ([`swept_texts`]): on the corpus's
/// analysis on one thread, on a fresh analysis whose memo the threads fill
/// as they race, and on the first analysis again.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_view_reads_the_same_at_any_thread_count() {
    let c = &*CORPUS;
    let texts = swept_texts(c);
    let cores = std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get);
    let once = view_dumps(&c.program, &c.analysis, &texts, 1);
    let fresh = Analysis::compute(&c.program);
    let wide = view_dumps(&c.program, &fresh, &texts, cores);
    let again = view_dumps(&c.program, &c.analysis, &texts, 1);
    let differ = |other: &[u64]| {
        texts
            .iter()
            .zip(once.iter().zip(other))
            .filter(|(_, (x, y))| x != y)
            .map(|((e, _), _)| format!("{e:#x}"))
            .take(10)
            .collect::<Vec<_>>()
    };
    println!("{} views read on 1 and {cores} threads", texts.len());
    assert!(
        differ(&wide).is_empty(),
        "across threads: {:?}",
        differ(&wide)
    );
    assert!(
        differ(&again).is_empty(),
        "in one process: {:?}",
        differ(&again)
    );
}

/// Reads every function's text of the `BORER_DOGFOOD` binary as a view,
/// checks that each spells its text and ships only corroborated ids
/// ([`view_sweep::unborne`]), and prints the census.
///
/// The texts are the sweep's ([`swept_texts`]), so nothing decompiles
/// twice. The census counts call tokens, variables, labels, globals,
/// string literals (listing unlinked ones by cause and requiring at least
/// 95% of non-ambiguous string literals to link) and fields; a linked id
/// must name the thing its token spells, and a linked `field_0x<hex>` its
/// own offset, at a field start or a gap of its type's layout.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_view_spells_its_text_and_links_only_what_the_code_shows() {
    let c = &*CORPUS;
    let (p, a) = (&c.program, &c.analysis);
    let by = view_sweep::spellings(p, a);
    let (mut census, mut misspelled, mut bad) =
        (view_sweep::Census::default(), Vec::new(), Vec::new());
    let started = std::time::Instant::now();
    for (entry, text) in swept_texts(c) {
        let Some(v) = view_of(p, a, &Overlay::default(), entry, text) else {
            misspelled.push(format!("{entry:#x}: no view"));
            continue;
        };
        if v.spell() != text && misspelled.len() < 10 {
            misspelled.push(format!("{entry:#x}"));
        }
        bad.extend(view_sweep::unborne(p, a, entry, &v, text));
        census.add(p, a, entry, &v, &by);
    }
    let share = |(n, k): (usize, usize)| format!("{k} of {n}");
    println!(
        "binary: {}\nviews: {:?}\ncall tokens: {} linked; resolvable: {} linked; ambiguous {}\nfirst resolvable unlinked: {:?}\nvariables: {} linked; labels: {} linked; globals: {} linked\nstrings: {} linked; resolvable: {} linked (unlinked causes: {:?}, samples: {:?})\nfields: {} linked; field_0x: {} linked\nthe views counted: {} uncorroborated, {} ambiguous",
        c.path,
        started.elapsed(),
        share(census.calls),
        share(census.resolvable),
        census.ambiguous,
        census.examples,
        share(census.kinds[0]),
        share(census.kinds[1]),
        share(census.kinds[2]),
        share(census.kinds[3]),
        share(census.resolvable_strings),
        census.string_causes,
        census.string_examples,
        share(census.kinds[4]),
        share(census.field_hex),
        census.counted.0,
        census.counted.1,
    );
    assert!(
        misspelled.is_empty(),
        "views that do not spell their text: {misspelled:?}"
    );
    assert!(
        bad.is_empty(),
        "{} ids no fact bears out: {:?}",
        bad.len(),
        &bad[..bad.len().min(10)]
    );
    assert!(
        census.resolvable_strings.0 == 0
            || census.resolvable_strings.1 * 100 >= census.resolvable_strings.0 * 95,
        "fewer than 95% of non-ambiguous string literals linked: {} (total {}, causes: {:?})",
        share(census.resolvable_strings),
        share(census.kinds[3]),
        census.string_causes
    );
}

/// Tells whether a name has the shape the engine spells a placeholder in.
///
/// Those are `sub_<hex>`, `L_<hex>`, `field_0x<hex>`, `g<bits>_<hex>`, `aN`, `vN`,
/// `local_<hex>`, `local_m<hex>`, `home_<hex>`, `arg_<hex>` or `<dll>_ord<n>`.
///
/// # Arguments
///
/// * `word` - The name as a view spells it.
fn placeholder_shaped(word: &str) -> bool {
    let hex = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_hexdigit());
    let dec = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    [
        "sub_", "L_", "field_0x", "local_m", "local_", "home_", "arg_",
    ]
    .iter()
    .any(|p| word.strip_prefix(p).is_some_and(hex))
        || word.strip_prefix('a').is_some_and(dec)
        || word.strip_prefix('v').is_some_and(dec)
        || word
            .strip_prefix('g')
            .and_then(|r| r.split_once('_'))
            .is_some_and(|(bits, at)| dec(bits) && hex(at))
        || word.rsplit_once("_ord").is_some_and(|(_, n)| dec(n))
}

/// Every function's view of the `BORER_DOGFOOD` binary spells its text and
/// says a name is a placeholder exactly where its spelling shows it is one.
///
/// The views read the sweep's texts ([`swept_texts`]) under no overlay. A
/// name that says it is a placeholder must have a placeholder's shape
/// ([`placeholder_shaped`]), and a function spelled `sub_` of its own
/// entry or a label `L_` of its own block must say it is one. It prints
/// the referents by who stated their names and the view build time at p95
/// and worst, and lists at most 10 of the names it finds wrong.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_placeholder_names_what_nothing_else_names() {
    let c = &*CORPUS;
    let (p, a) = (&c.program, &c.analysis);
    let o = Overlay::default();
    let texts = swept_texts(c);
    let (mut bad, mut took, mut by) = (Vec::new(), Vec::new(), [0usize; 5]);
    for &(entry, text) in &texts {
        let started = std::time::Instant::now();
        let v = view_of(p, a, &o, entry, text);
        took.push(started.elapsed());
        let Some(v) = v else {
            bad.push(format!("{entry:#x}: no view"));
            continue;
        };
        if v.spell() != text {
            bad.push(format!("{entry:#x}: does not spell its text"));
        }
        let n = v.said_counts();
        for (sum, k) in by
            .iter_mut()
            .zip([n.user, n.stated, n.inferred, n.placeholder, n.unknown])
        {
            *sum += k;
        }
        for i in 0..v.lines() {
            let line = v.line(i).unwrap_or_default();
            for (span, kind, link) in v.tokens_said(i) {
                let Some((r, said)) = link else {
                    continue;
                };
                let word = line.get(span).unwrap_or_default();
                let placeholder = said == Some(Said::Placeholder);
                let own = if let Ref::Function(e) = r {
                    word == format!("sub_{e:x}")
                } else if let Ref::Address(va) = r {
                    kind == Kind::Label && word == format!("L_{va:x}")
                } else {
                    false
                };
                if placeholder && !placeholder_shaped(word) {
                    bad.push(format!("{entry:#x} line {i}: {word} is no placeholder"));
                }
                if own && !placeholder {
                    bad.push(format!("{entry:#x} line {i}: {word} says {said:?}"));
                }
            }
        }
    }
    took.sort_unstable();
    let p95 = took.get(took.len().saturating_mul(95) / 100).copied();
    println!(
        "{} views: {} referents by who named them: user {}, stated {}, inferred {}, placeholder {}, unknown {}; build p95 {p95:?}, worst {:?}",
        texts.len(),
        by.iter().sum::<usize>(),
        by[0],
        by[1],
        by[2],
        by[3],
        by[4],
        took.last()
    );
    assert!(
        bad.is_empty(),
        "{} views or names wrong: {:?}",
        bad.len(),
        &bad[..bad.len().min(10)]
    );
}

/// Every function's listing view of the `BORER_DOGFOOD` binary answers
/// the addresses its blocks decode to.
///
/// Line by line, in order, and each instruction's line is found again; it
/// prints the build time at p95 and worst and the heap the views hold.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_listing_line_answers_the_instruction_it_shows() {
    let c = &*CORPUS;
    let (p, a) = (&c.program, &c.analysis);
    let o = Overlay::default();
    let (mut bad, mut took, mut heap) = (Vec::new(), Vec::new(), 0usize);
    for f in &a.functions {
        let started = std::time::Instant::now();
        let v = render::disasm_view(p, a, &o, f.entry, usize::MAX, render::Bytes::Hidden);
        took.push(started.elapsed());
        let Some(v) = v else {
            bad.push(format!("{:#x}: no view", f.entry));
            continue;
        };
        heap = heap.saturating_add(v.bytes());
        let decoded: Vec<u64> = f
            .blocks
            .iter()
            .flat_map(|b| render::block_instructions(p, b, u64::MAX))
            .collect();
        let shown: Vec<u64> = (0..v.lines()).filter_map(|i| v.address(i)).collect();
        let lost = shown
            .iter()
            .find(|&&va| v.line_of(va).and_then(|i| v.address(i)) != Some(va));
        if shown != decoded || lost.is_some() {
            bad.push(format!("{:#x}: lost {lost:x?}", f.entry));
        }
    }
    took.sort_unstable();
    let p95 = took.get(took.len().saturating_mul(95) / 100).copied();
    println!(
        "{} listing views: build p95 {p95:?}, worst {:?}; {heap} heap bytes",
        took.len(),
        took.last()
    );
    assert!(
        bad.is_empty(),
        "{} listings whose lines lose their instructions: {:?}",
        bad.len(),
        &bad[..bad.len().min(10)]
    );
}

/// Every linear instruction line is its function listing's line.
///
/// Every instruction line of the `BORER_DOGFOOD` binary's linear listing
/// is its function listing's line byte for byte, and every instruction a
/// function listing shows has its line there, but for those another block
/// owns the bytes of (an overlap, or past a block's row table), which it
/// names.
///
/// Every function, no sample: the listing is paged from the image's start
/// to its end at the most rows a page holds, and it prints the pages and
/// their build time at p95 and worst.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_linear_instruction_line_is_its_function_listing_line() {
    let c = &*CORPUS;
    let (p, a) = (&c.program, &c.analysis);
    let o = Overlay::default();
    let mut want: BTreeMap<u64, String> = BTreeMap::new();
    for f in &a.functions {
        let Some(v) = render::disasm_view(p, a, &o, f.entry, usize::MAX, render::Bytes::Hidden)
        else {
            continue;
        };
        for i in 0..v.lines() {
            if let (Some(va), Some(line)) = (v.address(i), v.line(i)) {
                want.entry(va).or_insert_with(|| line.to_owned());
            }
        }
    }
    let (mut seen, mut bad, mut took) = (BTreeSet::new(), Vec::new(), Vec::new());
    let mut rows: Vec<render::Row> = Vec::new();
    let mut at = Some(0);
    while let Some(va) = at {
        let started = std::time::Instant::now();
        let Some(page) = render::linear(p, a, &o, va, render::Dir::Next, render::LINES_MAX) else {
            bad.push(format!("{va:#x}: no page"));
            break;
        };
        took.push(started.elapsed());
        let v = &page.view;
        for i in 0..v.lines() {
            let (Some(va), Some(line)) = (v.address(i), v.line(i)) else {
                continue;
            };
            let Some(listed) = want.get(&va).filter(|_| line.starts_with("0x")) else {
                continue;
            };
            seen.insert(va);
            if line != listed {
                bad.push(format!("{va:#x}: {line:?} vs {listed:?}"));
            }
        }
        rows.extend(page.rows);
        at = page.next;
    }
    took.sort_unstable();
    let p95 = took.get(took.len().saturating_mul(95) / 100).copied();
    println!(
        "{} linear pages: p95 {p95:?}, worst {:?}; {} of {} instruction lines compared",
        took.len(),
        took.last(),
        seen.len(),
        want.len()
    );
    let (mut hidden, mut missing) = (Vec::new(), Vec::new());
    for &va in want.keys().filter(|va| !seen.contains(*va)) {
        let k = rows.partition_point(|r| r.span.start <= va);
        let row = k.checked_sub(1).and_then(|k| rows.get(k));
        match row.map(|r| r.kind) {
            Some(render::RowKind::Instruction | render::RowKind::Cut) => hidden.push(va),
            _ => missing.push(va),
        }
    }
    println!(
        "{} instructions another block owns the bytes of: {:x?}",
        hidden.len(),
        &hidden[..hidden.len().min(10)]
    );
    assert!(
        bad.is_empty() && missing.is_empty(),
        "{} lines differ, {} missing: {:?} {:x?}",
        bad.len(),
        missing.len(),
        &bad[..bad.len().min(10)],
        &missing[..missing.len().min(10)]
    );
}

/// Every corpus control-flow graph draws clear and deterministically.
///
/// Every function's control-flow graph of the `BORER_DOGFOOD` binary covers
/// its listing rows, draws clear, shows the crossings it reports, and draws
/// the same from a fresh analysis on sixteen threads as on one.
///
/// It prints the layout time at p50, p95 and worst, the graphs cut, the
/// crossings before and after reduction, and the heap the graphs hold. The
/// time is not held to a bar here, where the sweeps run side by side: the
/// bench's `timings` holds the slowest layout to its bar alone.
#[test]
#[ignore = "set BORER_DOGFOOD to a binary path to run this sweep"]
fn every_cfg_covers_its_rows_draws_clear_and_the_same_on_any_thread_count() {
    let c = &*CORPUS;
    let (p, o) = (&c.program, Overlay::default());
    let entries: Vec<u64> = c.analysis.functions.iter().map(|f| f.entry).collect();
    let (mut bad, mut took, mut first) = (Vec::new(), Vec::new(), Vec::new());
    let (mut before, mut after, mut heap, mut cut) = (0usize, 0usize, 0usize, 0usize);
    for &entry in &entries {
        let g = match render::cfg(p, &c.analysis, &o, entry) {
            Ok(g) => g,
            Err(e) => {
                bad.push(format!("{entry:#x}: {e:#}"));
                first.push(None);
                continue;
            }
        };
        let graph = drawn::graph_of(&g, entry);
        let started = std::time::Instant::now();
        let again = render::layout(&graph);
        took.push((started.elapsed(), entry));
        let l = g.layout();
        if let Err(e) = drawn::rows(&g).and_then(|()| drawn::check(&graph, &l)) {
            bad.push(format!("{entry:#x}: {e}"));
        }
        if again != *l {
            bad.push(format!("{entry:#x}: laid out twice, drawn differently"));
        }
        (before, after) = (before + l.crossings_before, after + l.crossings);
        heap += g.bytes();
        cut += usize::from(g.cut.is_some());
        first.push(Some(drawn::cfg_digest(&g, entry)));
    }
    let threads = 16;
    let fresh = c.analysis.clone();
    let mut again = vec![None; entries.len()];
    std::thread::scope(|s| {
        let parts: Vec<_> = (0..threads)
            .map(|t| {
                let (entries, fresh, o) = (&entries, &fresh, &o);
                s.spawn(move || {
                    entries
                        .iter()
                        .enumerate()
                        .skip(t)
                        .step_by(threads)
                        .map(|(i, &e)| {
                            let d = render::cfg(p, fresh, o, e).ok();
                            (i, d.map(|g| drawn::cfg_digest(&g, e)))
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        for part in parts {
            for (i, d) in part.join().expect("a worker") {
                again[i] = d;
            }
        }
    });
    let differ: Vec<String> = entries
        .iter()
        .zip(first.iter().zip(&again))
        .filter(|(_, (a, b))| a != b)
        .map(|(e, _)| format!("{e:#x}"))
        .collect();
    took.sort_unstable();
    let at = |q: usize| took.get(took.len().saturating_mul(q) / 100).map(|t| t.0);
    let worst = took.last().copied();
    println!(
        "{} layouts ({cut} cut): p50 {:?}, p95 {:?}, worst {worst:x?}; crossings {before} before, {after} after; {heap} heap bytes",
        took.len(),
        at(50),
        at(95),
    );
    assert!(
        bad.is_empty(),
        "{} graphs broken: {:?}",
        bad.len(),
        &bad[..bad.len().min(10)]
    );
    assert!(
        differ.is_empty(),
        "{} graphs draw differently on {threads} threads: {:?}",
        differ.len(),
        &differ[..differ.len().min(10)]
    );
}
