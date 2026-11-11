//! The memo store: one build per result, its budget, and what an edit lets go.

use super::*;

/// A derived result is built once however many threads ask for it at once,
/// and a kind asked for with another key type keeps cells of its own.
///
/// The passes that read pseudo-C back ask for the same function's text from
/// every worker of a program-wide query; a second build of one result is a
/// second decompile, so the waiting threads take the first build's result.
#[test]
fn a_derived_result_is_built_once_for_every_thread_asking() {
    use borer_engine::analysis::Derived;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let derived = Derived::default();
    let builds = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..8 {
            scope.spawn(|| {
                let value = derived.get_or_build("answer", 7_u64, || {
                    builds.fetch_add(1, Ordering::SeqCst);
                    std::thread::sleep(std::time::Duration::from_millis(20));
                    42_u32
                });
                assert_eq!(*value, 42);
            });
        }
    });
    assert_eq!(builds.load(Ordering::SeqCst), 1);
    let other = derived.get_or_build("answer", "7".to_owned(), || 1_u32);
    assert_eq!(*other, 1, "another key type is another cell");
    assert_eq!(derived.held("answer"), 2);
    assert_eq!(derived.held("nothing"), 0);
}

/// Item results past the memo's budget go least recently asked for first,
/// and one asked for again is built again, the same; a result of the
/// program alone stays whatever the budget.
///
/// Recency is the order of the asks: a text asked for again outlives the
/// texts built after it, so an agent's working set stays while a sweep's
/// trail goes.
#[test]
fn item_results_past_the_budget_go_least_recently_asked_first() {
    use borer_engine::analysis::Derived;
    use std::cell::Cell;

    let derived = Derived::default();
    let builds = Cell::new(0);
    let text = |entry: u64| {
        derived.get_or_build_item(
            "text",
            7,
            entry,
            || {
                builds.set(builds.get() + 1);
                vec![entry; 128]
            },
            |v| v.capacity() * size_of::<u64>(),
        )
    };
    derived.get_or_build("program", (), || vec![0_u8; 4096]);
    for entry in 0..8 {
        text(entry);
    }
    let eight = derived.item_bytes();
    derived.set_budget(eight);
    assert_eq!(derived.held("text"), 8, "eight texts fit a budget of eight");
    text(0);
    text(8);
    assert!(derived.item_bytes() <= eight, "{derived:?}");
    assert_eq!(builds.get(), 9);
    assert_eq!(*text(8), vec![8; 128], "the newest stays");
    assert_eq!(*text(0), vec![0; 128], "the one asked for again stays");
    assert_eq!(builds.get(), 9);
    assert_eq!(
        *text(1),
        vec![1; 128],
        "the oldest went, and comes back the same"
    );
    assert_eq!(builds.get(), 10);
    derived.set_budget(0);
    assert_eq!(derived.held("text"), 0);
    assert_eq!(derived.item_bytes(), 0);
    assert_eq!(derived.held("program"), 1, "a program's result is no item");
}

/// A memo budget too small for a few functions' texts changes no answer.
///
/// Every decompile and summary of the fixture reads as under the default
/// budget, asked twice and again after a rename, while the item results
/// kept stay within the budget. The store lets a result go only where it
/// can be built again from the program, the names and its key alone, so a
/// session that evicts is one that recomputes, never one that answers
/// differently.
#[test]
fn a_tiny_memo_budget_changes_no_answer() {
    use borer_engine::analysis::EnumSource;
    use borer_engine::analysis::decompile::decompile_named;
    use borer_engine::analysis::render::function_summary;

    const BUDGET: usize = 4096;
    let p = fixture();
    let roomy = Analysis::compute(&p);
    let tight = Analysis::compute(&p);
    tight.derived.set_budget(BUDGET);
    let entries: Vec<u64> = roomy.functions.iter().map(|f| f.entry).collect();
    let answers = |a: &Analysis, o: &Overlay| -> Vec<Option<String>> {
        entries
            .iter()
            .flat_map(|&e| [decompile_named(&p, a, o, e), function_summary(&p, a, o, e)])
            .collect()
    };
    let mut o = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let first = answers(&roomy, &o);
    assert_eq!(answers(&tight, &o), first);
    assert_eq!(answers(&tight, &o), first, "built again after letting go");
    o.names.insert(0x1020, "renamed".to_owned());
    let renamed = answers(&roomy, &o);
    assert_ne!(renamed, first, "the rename shows");
    assert_eq!(answers(&tight, &o), renamed);
    assert!(tight.derived.item_bytes() <= BUDGET, "{:?}", tight.derived);
    assert!(
        tight.derived.held("plain_text") < roomy.derived.held("plain_text"),
        "texts were let go"
    );
}

/// Results read under names no longer in force are let go, and only those.
///
/// A program's own results stay, and so do those read under the names in
/// force, under either source of name tables, and under the empty overlay
/// the program-wide sweeps read under. A rename leaves every text and catalog read under the old names keyed by
/// a fingerprint nothing asks for again; the same names coming back (a
/// rename undone) find them gone and build them again. A session's first
/// rename lets go of what it read before it, with the binary's tables and
/// no names, though the sweeps' empty overlay stays.
#[test]
fn results_under_names_no_longer_in_force_are_let_go() {
    use borer_engine::analysis::{Derived, EnumSource};

    let derived = Derived::default();
    let with_tables = |o: &Overlay| Overlay {
        enum_source: EnumSource::Binary,
        ..o.clone()
    };
    let named = |name: &str| {
        let mut o = Overlay::default();
        o.names.insert(0x1000, name.to_owned());
        o
    };
    let (old, new) = (named("before"), named("after"));
    let (empty, first) = (Overlay::default(), with_tables(&Overlay::default()));
    derived.get_or_build("homes", (), || 1_u8);
    for o in [&old, &new, &with_tables(&new), &empty, &first] {
        derived.get_or_build_named("index", o.fingerprint(), (), || 2_u8);
        derived.get_or_build_item("text", o.fingerprint(), 0x1000_u64, || 3_u8, |_| 0);
    }
    derived.forget_names_but(&new);
    assert_eq!(derived.held("homes"), 1);
    assert_eq!(derived.held("index"), 3, "{derived:?}");
    assert_eq!(derived.held("text"), 3, "{derived:?}");
    let before = derived.get_or_build_named("index", first.fingerprint(), (), || 4_u8);
    assert_eq!(*before, 4, "the session before its first rename was let go");
    let again = derived.get_or_build_named("index", old.fingerprint(), (), || 4_u8);
    assert_eq!(*again, 4, "the old names' result was let go");
    for o in [&with_tables(&new), &empty] {
        let kept = derived.get_or_build_named("index", o.fingerprint(), (), || 4_u8);
        assert_eq!(*kept, 2, "the names in force kept theirs");
    }
}

/// An edit carries a result whose reads miss it over to the new names and
/// lets go of one that read the changed key, one that read the whole map,
/// and one that took a result that read the key.
///
/// The carried result is not built again: asked for under the new names it
/// is the result built under the old.
#[test]
fn an_edit_lets_go_of_only_the_results_that_read_what_it_changed() {
    use borer_engine::analysis::Derived;

    let derived = Derived::default();
    let mut old = Overlay::default();
    old.names.insert(0x10, "ten".to_owned());
    old.names.insert(0x20, "twenty".to_owned());
    let build = |o: &Overlay, tag: u8| {
        let names = o.fingerprint();
        let key = |k: u64| {
            derived.get_or_build_item("key", names, k, || (tag, o.names.get(&k).cloned()), |_| 0)
        };
        let outer = derived.get_or_build_item(
            "outer",
            names,
            0x10_u64,
            || (tag, key(0x10).1.clone()),
            |_| 0,
        );
        let whole = derived.get_or_build_named("whole", names, (), || (tag, o.names.len()));
        let comment = derived.get_or_build_item(
            "comment",
            names,
            0x30_u64,
            || (tag, o.comments.contains_key(&0x30)),
            |_| 0,
        );
        (key(0x10).0, key(0x20).0, outer.0, whole.0, comment.0)
    };
    assert_eq!(build(&old, 1), (1, 1, 1, 1, 1));
    let mut new = old.clone();
    new.names.insert(0x20, "renamed".to_owned());
    derived.moved(&Analysis::default(), &old, &new);
    assert_eq!(
        build(&new, 2),
        (1, 2, 1, 2, 1),
        "the reads of 0x10 and of comments were carried; 0x20 and the whole map were built again"
    );
    let mut commented = new.clone();
    commented.comments.insert(0x30, "note".to_owned());
    derived.moved(&Analysis::default(), &new, &commented);
    assert_eq!(build(&commented, 3), (1, 2, 1, 2, 3));
    let mut gone = commented.clone();
    gone.names.remove(&0x10);
    derived.moved(&Analysis::default(), &commented, &gone);
    assert_eq!(
        build(&gone, 4),
        (4, 2, 4, 4, 3),
        "the outer result took the key's result, so it read 0x10 too"
    );
}

/// After every edit, an analysis that carried what the edit did not touch
/// decompiles every function to the bytes a fresh analysis builds.
///
/// It also rebuilds no more results than the fresh one does, and fewer
/// after some edit.
///
/// The edits are those an agent makes: renames of a called function, of a
/// function nothing calls and of a global, a comment, a type applied at a
/// global, a stated prototype, a rename undone, and an edit that changes
/// nothing.
#[test]
fn an_incremental_decompile_after_each_edit_matches_a_full_recompute() {
    use borer_engine::analysis::decompile::decompile_named;
    use borer_engine::analysis::protos::Proto;
    use borer_engine::analysis::utypes::parse_type;
    use borer_engine::analysis::{Derived, EnumSource};

    let p = fixture();
    let a = Analysis::compute(&p);
    let mut full = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    let called_by_another = |e: u64| {
        a.xrefs_to(e)
            .iter()
            .any(|r| r.from_entry.is_some_and(|from| from != e))
    };
    let called = entries
        .iter()
        .copied()
        .find(|&e| called_by_another(e))
        .expect("a called function");
    let lonely = entries
        .iter()
        .copied()
        .rev()
        .find(|&e| !called_by_another(e))
        .expect("a function nothing calls");
    type EditFn = Box<dyn Fn(&mut Overlay)>;
    let edits: Vec<EditFn> = vec![
        Box::new(move |o| {
            o.names.insert(called, "callee_renamed".to_owned());
        }),
        Box::new(move |o| {
            o.names.insert(lonely, "lonely_renamed".to_owned());
        }),
        Box::new(move |o| {
            o.comments.insert(lonely, "a note".to_owned());
        }),
        Box::new(move |o| {
            o.names.insert(0x2040, "greeting".to_owned());
        }),
        Box::new(move |o| {
            o.applied.insert(0x2040, parse_type("char *").unwrap());
        }),
        Box::new(move |o| {
            o.prototypes
                .insert(called, Proto::parse("int f(int a, int b)").unwrap());
        }),
        Box::new(move |o| {
            o.names.remove(&called);
        }),
        Box::new(|_| {}),
    ];
    let mut o = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    for &e in &entries {
        decompile_named(&p, &a, &o, e);
    }
    let mut carried_any = false;
    for (i, edit) in edits.iter().enumerate() {
        let before = o.clone();
        edit(&mut o);
        a.derived.moved(&a, &before, &o);
        let start = a.derived.builds();
        let texts: Vec<_> = entries
            .iter()
            .map(|&e| decompile_named(&p, &a, &o, e))
            .collect();
        let rebuilt = a.derived.builds() - start;
        full.derived = Derived::default();
        let fresh: Vec<_> = entries
            .iter()
            .map(|&e| decompile_named(&p, &full, &o, e))
            .collect();
        for ((e, mine), theirs) in entries.iter().zip(&texts).zip(&fresh) {
            assert_eq!(
                mine, theirs,
                "edit {i}: {e:#x} differs from a full recompute"
            );
        }
        let built = full.derived.builds();
        assert!(rebuilt <= built, "edit {i}: rebuilt {rebuilt} of {built}");
        carried_any |= rebuilt < built;
    }
    assert!(carried_any, "no edit carried a result over");
}

/// The callgraph walks callers as well as callees.
///
/// Asking what a function calls answers "what does this do"; asking what calls
/// it answers "what makes this happen", which is the question a network send or
/// a reward path raises. The reverse walk is transitive, so the chain above a
/// leaf comes back in one call, and its arrows still run the way calls do.
/// The fingerprint answer is a digest, and the manifest stays a file.
///
/// One line per function is megabytes on a real client, which is a sidecar to
/// put beside a build and not an answer to read. The digest settles the
/// question the manifest is usually opened for - are these the same functions
/// with the same bodies - in three lines.
#[test]
fn a_fingerprint_answer_is_a_digest_and_not_the_manifest() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let digest = borer_engine::analysis::render::fingerprint_digest(&a);
    let manifest = borer_engine::analysis::render::fingerprint_tsv(&a);
    assert!(digest.len() < manifest.len(), "{digest}");
    assert!(digest.contains("borer fingerprint v1 digest"), "{digest}");
    assert!(
        digest.lines().count() <= 4,
        "the answer is a few lines: {digest}"
    );
    assert!(
        !digest.contains(&format!("{:#x}	", a.functions[0].entry)),
        "the manifest's rows are not in the answer: {digest}"
    );
}

/// The digest moves when a fingerprint would, and not otherwise.
#[test]
fn a_fingerprint_digest_follows_the_manifest() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let once = borer_engine::analysis::render::fingerprint_digest(&a);
    let twice = borer_engine::analysis::render::fingerprint_digest(&a);
    assert_eq!(once, twice, "the digest is not stable");
    let mut moved = Analysis::compute(&p);
    moved.functions[0].body_hash ^= 1;
    let after = borer_engine::analysis::render::fingerprint_digest(&moved);
    assert_ne!(once, after, "a changed body left the digest where it was");
}

/// A wide root does not spend the whole node budget on its own children,
/// and the budget is not left unspent either.
///
/// Filling the budget breadth-first turns the graph into a star: every node
/// is a direct callee, no edge goes deeper, and the result says nothing that
/// the flat callee list in a summary does not already say. Capping every
/// node's fan-out instead leaves budget unused while callees go unshown.
#[test]
fn callgraph_reserves_budget_for_depth() {
    let a = Analysis::compute(&fixture());
    let root = a
        .functions
        .iter()
        .filter(|f| {
            f.callees
                .iter()
                .any(|c| a.function(*c).is_some_and(|g| !g.callees.is_empty()))
        })
        .max_by_key(|f| f.callees.len())
        .expect("a fixture function calls one that calls on");
    let p = fixture();
    let out = borer_engine::analysis::render::callgraph_mermaid(
        &p,
        &a,
        &Overlay::default(),
        root.entry,
        30,
        false,
    );
    let mut fanout: BTreeMap<&str, usize> = BTreeMap::new();
    for line in out.lines() {
        if let Some((from, _)) = line.trim().split_once(" --> ") {
            *fanout.entry(from).or_default() += 1;
        }
    }
    assert!(
        fanout.keys().any(|k| *k != "n0"),
        "the graph is a star, no edge leaves a non-root node:\n{out}"
    );
    let nodes = out
        .lines()
        .filter(|l| l.trim_start().starts_with('n') && l.contains('['))
        .count();
    assert!(
        !out.contains("not shown") || nodes == 30,
        "callees were held back with budget to spare ({nodes} nodes):\n{out}"
    );
}
