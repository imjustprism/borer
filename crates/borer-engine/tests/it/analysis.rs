//! Analysis tests on the hand-assembled fixture (see `common`): discovery,
//! blocks, edges, jump tables, cross-references, names and rendering.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::common;
use crate::decompiled;
use crate::fixture_pack;

use borer_engine::analysis::{Analysis, NameSource, Overlay, RefKind, name_of};
use borer_engine::num::from_usize;
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
use common::fixture;
use decompiled::decompiled;
use fixture_pack::fixture_pack;
use std::collections::BTreeMap;

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

/// The xrefs header's count reconciles with the rows under it.
///
/// A group is one row, the function's sites on it, so what the header
/// shows is what the offset pages; a header that counted one unit and
/// printed another left a reader unable to tell which unit to ask in.
#[test]
fn the_xrefs_header_counts_the_rows_it_prints() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = borer_engine::analysis::render::xrefs_tsv(&a, &o, 0x2040, 0, 60, false);
    let head = out.lines().next().unwrap_or_default();
    let rows = out
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .count();
    let claimed = head
        .split_once("showing ")
        .and_then(|(_, r)| r.split_once(' '))
        .and_then(|(n, _)| n.parse::<usize>().ok())
        .unwrap_or_else(|| panic!("header states no row count: {head}"));
    assert_eq!(
        claimed, rows,
        "header says {claimed} rows, printed {rows}: {out}"
    );
}

/// Asking only for the count says how many, and prints no rows to count.
#[test]
fn an_xrefs_count_only_answer_is_one_line() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let out =
        borer_engine::analysis::render::xrefs_tsv(&a, &Overlay::default(), 0x2040, 0, 60, true);
    assert_eq!(out.lines().count(), 1, "{out}");
    assert!(out.contains("xrefs to 0x2040"), "{out}");
    assert!(!out.contains("showing"), "a count states no page: {out}");
}

/// A reachability query answers with the chain, not with a neighbourhood.
///
/// A rendered call graph is capped so it stays readable, so on a real binary it
/// shows the functions around one function rather than the path between two.
/// The question it is usually opened for - does this ever get to the send, the
/// allocator, this check - wants a chain, and a chain is a few lines however
/// large the program is.
#[test]
fn a_call_path_finds_the_chain_between_two_functions() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let caller = a
        .functions
        .iter()
        .find(|f| !f.callees.is_empty())
        .expect("a fixture function that calls something");
    let callee = caller.callees[0];
    let out = borer_engine::analysis::render::call_path(&p, &a, &o, caller.entry, callee, 24);
    assert!(out.contains("reaches"), "{out}");
    assert!(out.contains("in 1 call(s)"), "{out}");
    assert!(
        out.contains(&format!("{:#x}", caller.entry)) && out.contains(&format!("{callee:#x}")),
        "the chain names both ends: {out}"
    );
}

/// A function reaches itself trivially, and the answer says so rather than
/// walking the graph to prove it.
#[test]
fn a_call_path_to_itself_is_answered_without_a_search() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let f = a.functions.first().expect("a fixture function");
    let out = borer_engine::analysis::render::call_path(
        &p,
        &a,
        &Overlay::default(),
        f.entry,
        f.entry,
        24,
    );
    assert!(out.contains("itself"), "{out}");
}

/// When there is no chain the answer says how far it looked, because "no" is
/// only worth anything with the search behind it.
#[test]
fn a_call_path_that_finds_nothing_says_how_far_it_looked() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let leaf = a
        .functions
        .iter()
        .find(|f| f.callees.is_empty())
        .expect("a fixture leaf");
    let other = a
        .functions
        .iter()
        .find(|f| f.entry != leaf.entry)
        .expect("a second fixture function");
    let out = borer_engine::analysis::render::call_path(&p, &a, &o, leaf.entry, other.entry, 24);
    assert!(out.contains("does not reach"), "{out}");
    assert!(out.contains("function(s) looked at"), "{out}");
}

#[test]
fn a_callgraph_walks_callers_as_well_as_callees() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let leaf = a
        .functions
        .iter()
        .find(|f| !f.callers.is_empty() && !f.callees.is_empty())
        .expect("a fixture function with both a caller and a callee");
    let o = Overlay::default();
    let up = borer_engine::analysis::render::callgraph_mermaid(&p, &a, &o, leaf.entry, 30, true);
    let down = borer_engine::analysis::render::callgraph_mermaid(&p, &a, &o, leaf.entry, 30, false);
    assert!(up.contains("callers of the root"), "{up}");
    assert!(down.contains("callees of the root"), "{down}");
    let caller = name_of(&a, &o, leaf.callers[0]);
    assert!(
        up.contains(caller.as_str()),
        "the caller is missing from the reverse graph:\n{up}"
    );
    assert!(up.contains(" --> "), "no edges drawn:\n{up}");
}

/// A TLS singleton reads as its class on both sides of a branch.
///
/// A runtime caches every manager in a thread-local block and reaches one as
/// `block[slot]`. The lifter folds such a read into the singleton's name, but
/// only while the block's register still carries the value inline: after a
/// branch, where the register has been written out and the join merges the
/// environments, the same access fell back to `*(uint64_t*)(0x58 + rbx)`.
/// On one client that left every manager unreadable.
///
/// The fixture loads the block, reads slot 0x58 before a branch and again
/// after the join; both must name the class.
#[test]
fn a_tls_singleton_reads_as_its_class_after_a_join() {
    let code: [u8; 41] = [
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x1c, 0xc8, 0xbf, 0x58,
        0x00, 0x00, 0x00, 0x48, 0x8b, 0x14, 0x1f, 0x48, 0x85, 0xd2, 0x74, 0x05, 0xe8, 0x08, 0x00,
        0x00, 0x00, 0x48, 0x8b, 0x04, 0x1f, 0x48, 0x01, 0xd0, 0xc3, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x2000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    let mut a = Analysis::compute(&p);
    a.classes.tls_slots.insert(0x58, "App::World".to_owned());
    let o = Overlay::default();
    let text =
        borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(
        text.contains("App::World"),
        "the slot did not read as its singleton:\n{text}"
    );
    assert!(
        !text.contains("+ rbx") && !text.contains("rbx +"),
        "the slot still reads as a raw offset from the block:\n{text}"
    );
}

/// A jump table's targets are case blocks, not functions of their own.
///
/// `JTG`'s table holds absolute addresses, which look like the data
/// pointers phase 2 seeds from; each is a block inside `JTG`.
#[test]
fn jump_table_targets_do_not_become_functions() {
    let p = fixture();
    let a = Analysis::compute(&p);
    for target in [0x4cbeu64, 0x4cc4, 0x4cca] {
        assert!(
            a.function(target).is_none(),
            "case block {target:#x} became a function"
        );
    }
}

/// A virtual method no signature string named takes its slot's name.
///
/// `Base`'s table holds `Q` at slot 1 and no assert names it, so it becomes
/// `Base::vfunc_1` and every call to it reads that way.
#[test]
fn unnamed_vtable_slots_take_their_class_and_index() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let f = a.function(0x11e0).expect("the slot function");
    assert_eq!(f.name.as_deref(), Some("Base::vfunc_1"), "{:?}", f.name);
    assert!(f.name_inferred);
    assert_eq!(f.name_source, NameSource::Slot);
}

/// An assert that names a method does not name the field it reads.
///
/// `LKC` asserts `this->IsSet()`, so the field at 8 is what `IsSet` reads,
/// not a member called `IsSet`; rendering it `this->IsSet()` would put a
/// call in the text where the code reads memory, so it stays an offset.
#[test]
fn a_method_named_in_an_assert_does_not_name_a_field() {
    use borer_engine::analysis::classes::field_names;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let names = field_names(&p, &a, &o, "Lk");
    assert!(names.is_empty(), "a method is not a member: {names:?}");
}

/// A class's fields read the same in every answer that labels them.
///
/// `Lk::Chk`'s only assert reads the field at 8 through `this->IsSet()`, so
/// the layout and the field's typed uses both label it by that getter,
/// `IsSet()`, while the decompiler's member names leave it out (see the
/// test above). `Arr<char>`'s field at 8 is `size` by its template
/// sibling's assert, in its layout as in its member names.
#[test]
fn a_field_reads_the_same_label_in_every_answer() {
    use borer_engine::analysis::classes::{
        class_layout, field_names, render_layout, typed_field_uses,
    };
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let lk = render_layout(&class_layout(&p, &a, &o, "Lk").expect("Lk"), &a, &o);
    assert!(
        lk.lines()
            .any(|l| l.starts_with("+0x8 ") && l.contains(" IsSet() ")),
        "{lk}"
    );
    let uses = typed_field_uses(&p, &a, &o, "Lk", 8).expect("Lk is a class");
    assert_eq!(uses.name.as_deref(), Some("IsSet()"));
    let arr = render_layout(
        &class_layout(&p, &a, &o, "Arr<char>").expect("Arr<char>"),
        &a,
        &o,
    );
    assert!(
        arr.lines()
            .any(|l| l.starts_with("+0x8 ") && l.contains(" size ")),
        "{arr}"
    );
    assert_eq!(
        field_names(&p, &a, &o, "Arr<char>")
            .get(&8)
            .map(String::as_str),
        Some("size")
    );
}

/// A template's instantiations pool the names their asserts give.
///
/// `Arr<char>`'s one method asserts nothing, but `Arr<int>` proves the same
/// template puts `size` at 8, and every instantiation of a template that
/// holds its elements by pointer lays them out the same way.
#[test]
fn instantiations_share_the_field_names_of_their_template() {
    use borer_engine::analysis::classes::field_names;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        field_names(&p, &a, &o, "Arr<int>")
            .get(&8)
            .map(String::as_str),
        Some("size"),
        "the instantiation that asserts names its own field"
    );
    assert_eq!(
        field_names(&p, &a, &o, "Arr<char>")
            .get(&8)
            .map(String::as_str),
        Some("size"),
        "the one that does not takes the name from its sibling"
    );
}

/// A class's field labels follow the names in force: asked again after a
/// rename, the class answers what a fresh session asked once would.
///
/// `Arr<char>` takes `size` at 8 from its template sibling `Arr<int>::Add`.
/// Renamed out of the template, the sibling names nothing; with the rename
/// dropped it names `size` again, though `Arr<char>`'s own methods never
/// changed.
#[test]
fn field_labels_follow_the_names_in_force() {
    use borer_engine::analysis::classes::{FieldLabel, field_labels};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut renamed = Overlay::default();
    renamed.names.insert(0x4e50, "Other::Add".to_owned());
    let label = |o: &Overlay| field_labels(&p, &a, o, "Arr<char>").remove(&8);
    assert_eq!(label(&renamed), None, "no sibling names the field");
    let fresh = field_labels(&p, &Analysis::compute(&p), &Overlay::default(), "Arr<char>");
    assert_eq!(fresh.get(&8), Some(&FieldLabel::Member("size".to_owned())));
    assert_eq!(label(&Overlay::default()).as_ref(), fresh.get(&8));
}

/// One function's field accesses come back keyed by base and offset.
///
/// `CM` reads `[rcx+0x10]`, `[rcx+0x14]` and `[rcx+0x18]` as 32-bit fields off
/// its first argument, so `fields_tsv` reports three read rows at those offsets
/// with a 4-byte width. This is the per-function offset table an SDK checks its
/// `@derive` anchors against.
#[test]
fn field_accesses_of_a_function_list_offset_width_and_direction() {
    use borer_engine::analysis::classes::{field_accesses, fields_tsv};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let sites = field_accesses(&p, &a, &o, 0x5200).expect("CM decompiles");
    let base = sites
        .keys()
        .find(|(_, off)| *off == 0x10)
        .map(|(b, _)| b.clone())
        .expect("a field at 0x10");
    for off in [0x10u64, 0x14, 0x18] {
        let site = sites
            .get(&(base.clone(), off))
            .unwrap_or_else(|| panic!("no field {off:#x}: {sites:?}"));
        assert!(
            site.widths.contains(&32),
            "field {off:#x} not 32-bit: {site:?}"
        );
        assert!(
            site.reads > 0 && site.writes == 0,
            "field {off:#x} not a read: {site:?}"
        );
    }
    let tsv = fields_tsv(&p, &a, &o, 0x5200).expect("CM decompiles");
    assert!(
        tsv.contains(&format!("{base}\t0x10\t4\tr")),
        "tsv row missing:\n{tsv}"
    );
}

/// The recovered singletons list the class kept at each thread-local slot.
///
/// `Tls::Tls` registers its instance at a thread-local slot, so the singleton
/// registry names that class at a `tls` row. This is the program's global
/// object model — which one-of-a-kind objects it keeps and where.
#[test]
fn singletons_list_the_class_at_each_thread_local_slot() {
    use borer_engine::analysis::render::singletons_tsv;
    let p = fixture();
    let a = Analysis::compute(&p);
    let out = singletons_tsv(&a, &Overlay::default(), "");
    assert!(out.starts_with("# "), "no header:\n{out}");
    assert!(
        out.lines()
            .any(|l| l.starts_with("tls\t") && l.ends_with("Tls")),
        "the thread-local singleton was not recovered:\n{out}"
    );
    let filtered = singletons_tsv(&a, &Overlay::default(), "tls");
    assert!(
        filtered.contains("\tTls\n"),
        "filter dropped the match:\n{filtered}"
    );
}

/// An address code takes but never calls is still a function.
///
/// `TH` sits in the gap between `CS`'s two blocks, so it is inside `CS`'s
/// range and behind `int3` padding, where neither the pointer scan nor the
/// padding scan will look; `LT`'s `lea` is the only evidence it exists, and
/// that is how a registered callback's thunk is reached.
#[test]
fn an_address_code_takes_is_a_function() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let th = a
        .function(0x4ee0)
        .expect("the thunk the lea names is a function");
    assert_eq!(th.entry, 0x4ee0);
    assert_eq!(
        a.function(0x4ed0).map(|f| f.blocks.len()),
        Some(3),
        "the function it sits inside keeps its own blocks"
    );
}

/// A string search reads the whole string, not the start of it.
///
/// `SN` names a build path whose file name begins past the eightieth
/// character, which is what a real assertion's path looks like; matching
/// only the display text would hide every file in the image behind the
/// machine it was built on.
#[test]
fn a_string_search_sees_past_a_long_path_prefix() {
    use borer_engine::analysis::render::functions_by_string_tsv;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let hit = functions_by_string_tsv(&p, &a, &o, "needle.h", 0, 5);
    assert!(hit.contains("1 function/string pairs"), "{hit}");
    assert!(hit.contains("sub_5080"), "{hit}");
    assert!(hit.contains("probe/needle.h"), "{hit}");
}

/// A pointer to a function in data is a reference to it.
///
/// `Der`'s table at 0x22a0 holds `0x1870` in its first slot, and a virtual
/// method is reached that way and no other; without the tables, asking what
/// reaches it answers nothing.
#[test]
fn a_pointer_table_slot_references_the_function_it_holds() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let sites = a.xrefs_to(0x1870);
    let slot = sites
        .iter()
        .find(|s| s.kind == RefKind::Table)
        .expect("the table slot is a reference");
    assert_eq!(slot.va, 0x22a0);
    assert_eq!(slot.from_entry, None, "a table slot is data, not a caller");
}

/// A float field keeps its width when a wider store covers it.
///
/// `Fz::Set` zeroes eight bytes over the float at 0x10 and the one after
/// it, which is what a constructor does; taking the widest access would
/// call a four-byte float a double.
#[test]
fn a_float_field_is_not_widened_by_a_zeroing_store() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let fz = class_layout(&p, &a, &o, "Fz").expect("Fz layout");
    let text = render_layout(&fz, &a, &o);
    assert!(text.contains("+0x10   float"), "{text}");
}

/// The functions using a class's field are the ones holding a pointer typed
/// as the class, not every instruction at the offset.
///
/// `Der`'s field at 8 is read by `Der::Chk` through `this`, by `HT` through
/// the parameter its caller hinted `Der *`, by `Der2::Foo` through a derived
/// `this`, and copied by `Der::Cmp` from its `Der *` parameter into `this`.
/// `Cls::Set` writes and `Cls::Has` reads `[rcx+8]` too, of another class,
/// and stay out. Each row carries the instructions it was found at.
#[test]
fn a_class_field_lists_the_functions_using_it_through_a_typed_pointer() {
    use borer_engine::analysis::classes::{typed_field_uses, typed_field_uses_tsv};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let uses = typed_field_uses(&p, &a, &o, "Der", 8).expect("Der is a class");
    let rows: Vec<(u64, Vec<&str>, usize, usize)> = uses
        .uses
        .iter()
        .map(|u| {
            (
                u.entry,
                u.via.iter().map(String::as_str).collect(),
                u.field.reads,
                u.field.writes,
            )
        })
        .collect();
    assert_eq!(
        rows,
        vec![
            (0x1740, vec!["this"], 1, 0),
            (0x18d0, vec!["a1"], 1, 0),
            (0x19a0, vec!["this"], 1, 0),
            (0x19d0, vec!["a2", "this"], 1, 1),
        ],
        "{uses:?}"
    );
    assert_eq!(uses.derived, vec!["Der2".to_owned()]);
    assert_eq!(uses.name.as_deref(), Some("count"));
    let cmp = uses.uses.last().expect("Der::Cmp uses the field");
    assert_eq!(cmp.sites, vec![0x19d0, 0x19d3], "the load and the store");
    let tsv = typed_field_uses_tsv(&uses, &a, &o, 8, 0, 10, false);
    assert!(
        tsv.starts_with("# Der+0x8 count: 4 functions use it through a pointer typed as the class (a method's object, a typed parameter, a smart pointer's operator ->) or as a class derived from it (Der2): 1 stores, 4 loads, 0 address-takens, showing 4 from 0
"),
        "{tsv}"
    );
    assert!(tsv.contains("0x19d0	Der::Cmp	a2,this	rw	"), "{tsv}");
    assert!(!tsv.contains("Cls::"), "another class's field at 8: {tsv}");
}

/// A class registration records the code that identifies it on the wire.
///
/// `RG` hands a registrar `"Zz::Thing"` and `0x41424344`; without the code
/// a recovered message format has no name a reader could match a packet to.
#[test]
fn a_class_registration_records_its_wire_id() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(a.classes.ids.get("Zz::Thing").copied(), Some(0x4142_4344));
}

/// The registry lists every class that carries a wire code.
///
/// An agent asking what a four-character code in a packet belongs to, or
/// what code a class travels under, reads one table instead of decompiling
/// the registrar. `RG` registers `Zz::Thing` as `'ABCD'`.
#[test]
fn the_class_registry_lists_a_registered_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let all = borer_engine::analysis::render::class_ids_tsv(&a, "");
    assert!(all.contains("Zz::Thing"), "{all}");
    assert!(all.contains("'ABCD'"), "{all}");
    let row = all
        .lines()
        .find(|l| l.ends_with("Zz::Thing"))
        .expect("the registered class has a row");
    assert!(
        row.starts_with("'ABCD'\t") && row.split('\t').count() == 4,
        "a row is the code, the method count, the first method and the class, tab-separated: {row}"
    );
    assert!(all.contains("# code\tmethods\tfirst\tclass\n"), "{all}");
    let filtered = borer_engine::analysis::render::class_ids_tsv(&a, "abcd");
    assert!(filtered.contains("Zz::Thing"), "{filtered}");
    assert!(
        !borer_engine::analysis::render::class_ids_tsv(&a, "nothinghere").contains("Zz::Thing"),
        "the filter let everything through"
    );
}

/// The source tree groups the functions by the file that asserts.
///
/// A reader opening an unknown binary asks which subsystems it was built
/// from before asking about any function. The fixture cites
/// `C:\ws\code\foundation\util/fourcc.h` and `src/ah.cc`, and the build
/// root the first carries is dropped.
#[test]
fn the_source_tree_groups_functions_by_file() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let dirs = borer_engine::analysis::render::source_tree_tsv(&p, &a, "");
    assert!(dirs.contains("directory"), "{dirs}");
    assert!(dirs.contains("fourcc.h") || dirs.contains("util"), "{dirs}");
    assert!(
        dirs.contains("# base: C:/\n"),
        "the build root is written once: {dirs}"
    );
    let files = borer_engine::analysis::render::source_tree_tsv(&p, &a, "fourcc");
    assert!(files.contains("fourcc.h"), "{files}");
    assert!(
        files.contains("# base: C:/\n"),
        "the build root is written once: {files}"
    );
    assert!(
        files
            .lines()
            .any(|l| l.ends_with("\tws/code/foundation/util/fourcc.h")
                && l.starts_with(|c: char| c.is_ascii_digit())
                && l.split('\t').count() == 3),
        "a row is the functions, the first and the file, tab-separated: {files}"
    );
    assert!(
        !files
            .lines()
            .any(|l| !l.starts_with('#') && l.contains("C:/ws")),
        "the build root is still in a row: {files}"
    );
}

/// The assertion index says which classes name a field.
///
/// A reader who meets `state` in one class wants the others that call a
/// field by that name, which the assertions say and no symbol does. `AS`
/// asserts `this->head`, `GG` asserts `this->tail`.
#[test]
fn the_assertion_index_lists_a_named_field() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let all = borer_engine::analysis::render::asserted_fields_tsv(&p, &a, &o, "");
    assert!(all.contains("head") || all.contains("tail"), "{all}");
    let one = borer_engine::analysis::render::asserted_fields_tsv(&p, &a, &o, "tail");
    assert!(one.contains("tail"), "{one}");
    assert!(
        one.contains("this->tail"),
        "the filtered listing does not say what is asserted: {one}"
    );
    assert!(
        one.lines()
            .any(|l| l.starts_with(|c: char| c.is_ascii_digit())
                && l.contains("\ttail\t")
                && l.split('\t').count() == 3),
        "a row is the functions, the field and the classes, tab-separated: {one}"
    );
    assert!(
        one.lines()
            .any(|l| l.starts_with("\t") && l.contains("this->tail")),
        "a condition is one tab-indented line: {one}"
    );
    assert!(
        !one.contains(" head "),
        "the filter let everything through: {one}"
    );
}

/// The protection profile says whether reading the text is worth anything.
///
/// A packer leaves a name in its sections, a body that is all entropy, an
/// import table too thin to run, and megabytes of executable bytes with
/// almost no code in them. The fixture has none of that and says so.
#[test]
fn the_protection_profile_tells_packed_from_plain() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let plain = borer_engine::analysis::render::protection_tsv(&p, &a);
    assert!(plain.starts_with("# plain"), "{plain}");

    let mut bytes = vec![0xccu8; 0x1000];
    let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
    bytes.extend((0..0x40000).map(|_| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        u8::try_from(seed >> 56).unwrap_or(0)
    }));
    let packed = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".vmp0", 0x1000, 0x1000, 0x40000, true, true,
        )],
    );
    let pa = Analysis::compute(&packed);
    let text = borer_engine::analysis::render::protection_tsv(&packed, &pa);
    assert!(text.starts_with("# protected: VMProtect"), "{text}");
    assert!(text.contains("entropy 7.2 or above"), "{text}");
    assert!(text.contains("writable and executable"), "{text}");
}

/// A dispatch loop is found and its handlers described.
///
/// An interpreter fetches an operation, jumps through a table to the code
/// for it, and comes back; a virtualizing protector leaves exactly that
/// where the original function used to be. The machine here has sixteen
/// handlers, each adding its own number and jumping back, which is the
/// smallest thing that has the shape.
#[test]
fn a_dispatch_loop_is_found_with_its_handlers() {
    const TABLE: u64 = 0x8000;
    const FIRST: u64 = 0x1020;
    let mut bytes = vec![0xccu8; 0x1000];
    bytes.extend_from_slice(&[
        0x48, 0x8d, 0x35, 0xf9, 0x70, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x48, 0xff, 0xc6, 0x83, 0xf8,
        0x0f, 0x77, 0x07, 0xff, 0x24, 0xc5, 0x00, 0x80, 0x00, 0x00, 0xc3,
    ]);
    bytes.resize(usize::try_from(FIRST).unwrap_or(0), 0xcc);
    for i in 0..16u64 {
        let at = FIRST + i * 16;
        bytes.resize(usize::try_from(at).unwrap_or(0), 0xcc);
        let back = i32::try_from(0x1007i64 - i64::try_from(at + 9).unwrap_or(0)).unwrap_or(0);
        bytes.extend_from_slice(&[0x48, 0x83, 0xc3, u8::try_from(i).unwrap_or(0), 0xe9]);
        bytes.extend_from_slice(&back.to_le_bytes());
    }
    bytes.resize(usize::try_from(TABLE).unwrap_or(0), 0xcc);
    for i in 0..16u64 {
        bytes.extend_from_slice(&(FIRST + i * 16).to_le_bytes());
    }
    bytes.resize(0x9000, 0);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x7000, false, true),
            Section::mapped(".rdata", TABLE, TABLE, 0x1000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let list = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "").unwrap();
    assert!(list.starts_with("# 1 dispatch loop found"), "{list}");
    assert!(list.contains("      16 "), "{list}");
    let one = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(one.contains("16 handlers"), "{one}");
    let next = borer_engine::analysis::render::next_steps(&p, &a, &o, 0x1000);
    assert!(
        next.first()
            .is_some_and(|s| s.starts_with("borer://vm/0x1000 (a dispatch loop of 16 handlers")),
        "{next:?}"
    );
    assert!(
        one.contains("add"),
        "the handlers say nothing about what they do: {one}"
    );
    assert!(one.contains("0x1020"), "{one}");
    assert!(
        one.contains("read through rsi, pointed at 0x8100"),
        "the bytecode pointer and its address are not named: {one}"
    );
}

/// The image of a small interpreter: a rel32 dispatch over a program table.
///
/// Five handlers is what a hand-written VM of a dozen opcodes leaves, with
/// its table in read-only data below nothing and its handlers always below
/// the table (`lea r9, [PROG]; lea r11, [TABLE]; movzx ecx, byte [r9];
/// movsxd rcx, [r11+rcx*4]; jmp rcx`), so the entries are negative
/// offsets, and only their sign extension reads as targets. With
/// `fetch_from_memory` false the fetch becomes `mov ecx, esi`: the same
/// loop, the same table, an index the program computed instead of read.
const VM_PROG: u64 = 0x2000;
const VM_TABLE: u64 = 0x2010;
const VM_JMP: u64 = 0x102e;

/// Builds [`VM_PROG`]'s image; see its doc for the code.
///
/// # Panics
///
/// Never in practice: every displacement constant fits by construction.
///
/// # Arguments
///
/// * `fetch_from_memory` - Whether the dispatch fetches its opcode from
///   the program table or computes it from a register.
#[expect(
    clippy::unwrap_used,
    reason = "a fixture builder: every constant here fits by construction"
)]
fn small_vm(fetch_from_memory: bool) -> Program {
    let mut bytes = vec![0xccu8; 0x1000];
    let prog_to_lea = i32::try_from(VM_PROG - 0x1007).unwrap();
    let table_to_lea = i32::try_from(VM_TABLE - 0x100e).unwrap();
    let mut code: Vec<u8> = Vec::new();
    code.extend_from_slice(&[0x4c, 0x8d, 0x0d]);
    code.extend_from_slice(&prog_to_lea.to_le_bytes());
    code.extend_from_slice(&[0x4c, 0x8d, 0x1d]);
    code.extend_from_slice(&table_to_lea.to_le_bytes());
    code.extend_from_slice(&[0x31, 0xd2]);
    code.extend_from_slice(&[0x49, 0x83, 0xc1, 0x02]);
    code.extend_from_slice(&[0x49, 0x81, 0xf9]);
    code.extend_from_slice(&u32::try_from(VM_PROG + 12).unwrap().to_le_bytes());
    code.extend_from_slice(&[0x74, 0x2c]);
    if fetch_from_memory {
        code.extend_from_slice(&[0x41, 0x0f, 0xb6, 0x09]);
    } else {
        code.extend_from_slice(&[0x8b, 0xce, 0x66, 0x90]);
    }
    code.extend_from_slice(&[0x48, 0x83, 0xf9, 0x04, 0x77, 0x22]);
    code.extend_from_slice(&[0x49, 0x63, 0x0c, 0x8b, 0x4c, 0x01, 0xd9, 0xff, 0xe1]);
    for i in 0..5u8 {
        code.extend_from_slice(&[0x83, 0xc2, 5 + i]);
        code.extend_from_slice(&[0xeb, 0xdb - i * 5]);
    }
    code.extend_from_slice(&[0x89, 0xd0, 0xc3]);
    bytes.extend_from_slice(&code);
    bytes.resize(usize::try_from(VM_PROG).unwrap(), 0xcc);
    bytes.extend_from_slice(&[3, 0, 0, 0x5a, 2, 3, 3, 0, 1, 0x33, 2, 7]);
    bytes.resize(usize::try_from(VM_TABLE).unwrap(), 0xcc);
    for i in 0..5u32 {
        let target =
            i32::try_from(0x1030 + u64::from(i) * 5).unwrap() - i32::try_from(VM_TABLE).unwrap();
        bytes.extend_from_slice(&target.to_le_bytes());
    }
    bytes.resize(0x3000, 0xcc);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    )
}

/// A rel32 jump table whose targets sit below its lea'd base resolves.
///
/// The entries are negative offsets, and reading them unsigned lands the
/// targets far outside every section, which is exactly the table a
/// hand-built interpreter over read-only data carries.
#[test]
fn a_rel32_table_with_targets_below_it_resolves() {
    let p = small_vm(true);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&VM_JMP),
        Some(&vec![0x1030, 0x1035, 0x103a, 0x103f, 0x1044]),
        "the negative rel32 entries did not read as their handlers"
    );
}

/// A synchronization wrapper that mentions a phrase and compares rwlock
/// state bits is a mention, never a check.
///
/// `FX` in the fixture image references an `is_unlocked` assertion and
/// compares against `0x40000000` and `0xc0000000`, the futex rwlock reader
/// and writer bits: a std wrapper every Rust binary carries, which once
/// stood as the only check a crackme listed.
#[test]
fn a_sync_bitmask_compare_is_not_a_check() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::render::license_checks_tsv(&p, &a, &Overlay::default());
    assert!(text.starts_with("# 0 functions judge"), "{text}");
    assert!(text.contains("sub_5c00 (unlock)"), "{text}");
    assert!(!text.contains("0x40000000"), "{text}");
    assert!(!text.contains("0xc0000000"), "{text}");
}

/// A check no phrase names is found by what it reads and what it tests.
///
/// `KC` in the fixture image calls `scanf` into the buffer its parameter
/// points at and compares a byte of what it read against the value the
/// call parsed: the shape of `check(key(name), serial)` with the keygen
/// math on one side and the input on the other, and not a string in it.
#[test]
fn an_unnamed_check_is_found_by_what_it_reads_and_tests() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::render::license_checks_tsv(&p, &a, &Overlay::default());
    assert!(
        text.starts_with(
            "# 0 functions judge a key, serial or license; 1 more test what they read"
        ),
        "{text}"
    );
    assert!(
        text.contains(
            "# 1 read input and test what they compute against it: sub_5c40 (a value it parsed)"
        ),
        "{text}"
    );
}

/// A dispatch of five handlers is found when it fetches its index from
/// memory, and the same loop with a computed index is not.
///
/// The first is an interpreter's shape: read the next opcode out of the
/// program, jump through the table for it, come back. The second is the
/// ordinary small `switch` the handler floor has always refused, and the
/// fetch is the only difference between them.
#[test]
fn a_small_dispatch_that_fetches_from_memory_is_found() {
    let p = small_vm(true);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let list = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "").unwrap();
    assert!(list.starts_with("# 1 dispatch loop found"), "{list}");
    assert!(list.contains("     5 "), "{list}");
    let one = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "0x102e").unwrap();
    assert!(one.contains("5 handlers"), "{one}");
    assert!(one.contains("add"), "the handlers say nothing: {one}");
    let plain = small_vm(false);
    let pa = Analysis::compute(&plain);
    let refused = borer_engine::analysis::render::vm_dispatch_tsv(&plain, &pa, &o, "").unwrap();
    assert!(refused.starts_with("# 0 dispatch loops found"), "{refused}");
}

/// A dispatch whose fetch is xored with a running key is named as one.
///
/// The machine here is `VoidVault v7.1`'s shape in miniature: the fetch reads
/// three operands through one base, the immediate is xored with `rbx` before
/// the jump, and every handler returns through a tail that calls a mixer,
/// xors its result with a register-file slot and writes it back into `rbx`.
/// The bytecode on disk is then noise for every run but the one that
/// produced it, and the view must say so rather than leave the reader to
/// discover it opcode by opcode.
///
/// # Panics
///
/// Never in practice: every displacement constant fits by construction.
#[test]
fn a_running_key_fetch_is_named_in_the_dispatch_view() {
    const TABLE: u64 = 0x8000;
    const PROG: u64 = 0x9000;
    const HANDLER: u64 = 0x1040;
    const TAIL: u64 = 0x10a0;
    const MIXER: u64 = 0x10b8;
    let mut bytes = vec![0xccu8; 0x1000];
    let mut code: Vec<u8> = Vec::new();
    code.extend_from_slice(&[0x4c, 0x8d, 0x0d]);
    code.extend_from_slice(&i32::try_from(PROG - 0x1007).unwrap().to_le_bytes());
    code.extend_from_slice(&[0x4c, 0x8d, 0x1d]);
    code.extend_from_slice(&i32::try_from(TABLE - 0x100e).unwrap().to_le_bytes());
    code.extend_from_slice(&[0x41, 0x0f, 0xb6, 0x11]);
    code.extend_from_slice(&[0x45, 0x0f, 0xb6, 0x51, 0x01]);
    code.extend_from_slice(&[0x49, 0x8b, 0x49, 0x04]);
    code.extend_from_slice(&[0x48, 0x31, 0xd9]);
    code.extend_from_slice(&[0x49, 0x83, 0xc1, 0x02]);
    code.extend_from_slice(&[0x80, 0xfa, 0x0b]);
    code.extend_from_slice(&[0x0f, 0x87]);
    code.extend_from_slice(&(i32::try_from(MIXER - 0x102b).unwrap()).to_le_bytes());
    code.extend_from_slice(&[0x49, 0x63, 0x14, 0x93]);
    code.extend_from_slice(&[0x4c, 0x01, 0xda]);
    code.extend_from_slice(&[0xff, 0xe2]);
    bytes.extend_from_slice(&code);
    for i in 0..12u8 {
        let at = HANDLER + u64::from(i) * 8;
        bytes.resize(usize::try_from(at).unwrap(), 0xcc);
        bytes.extend_from_slice(&[0x83, 0xc3, i]);
        let back = i32::try_from(TAIL - (at + 8)).unwrap();
        bytes.extend_from_slice(&[0xe9]);
        bytes.extend_from_slice(&back.to_le_bytes());
    }
    bytes.resize(usize::try_from(TAIL).unwrap(), 0xcc);
    bytes.extend_from_slice(&[0xe8]);
    bytes.extend_from_slice(&i32::try_from(MIXER - (TAIL + 5)).unwrap().to_le_bytes());
    bytes.extend_from_slice(&[0x4b, 0x33, 0x04, 0xa8]);
    bytes.extend_from_slice(&[0x48, 0x89, 0xc3]);
    bytes.extend_from_slice(&[0xe9]);
    bytes.extend_from_slice(
        &i32::try_from(0x100ei64 - i64::try_from(TAIL).unwrap() - 0x11)
            .unwrap()
            .to_le_bytes(),
    );
    bytes.resize(usize::try_from(MIXER).unwrap(), 0xcc);
    bytes.extend_from_slice(&[0xc3]);
    bytes.resize(usize::try_from(TABLE).unwrap(), 0xcc);
    for i in 0..12u64 {
        let entry = i32::try_from(HANDLER + i * 8).unwrap() - i32::try_from(TABLE).unwrap();
        bytes.extend_from_slice(&entry.to_le_bytes());
    }
    bytes.resize(usize::try_from(PROG).unwrap(), 0xcc);
    bytes.extend_from_slice(&[3, 0, 0, 0x5a, 2, 3, 3, 0, 1, 0x33, 2, 7]);
    bytes.resize(0xA000, 0);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x7000, false, true),
            Section::mapped(".rdata", TABLE, TABLE, 0x2000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let list = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "").unwrap();
    assert!(list.starts_with("# 1 dispatch loop found"), "{list}");
    let one = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(one.contains("12 handlers"), "{one}");
    assert!(
        one.contains("running-key fetch"),
        "the running key is not named: {one}"
    );
    assert!(
        one.contains("xored with rbx"),
        "the key register is not named: {one}"
    );
    assert!(
        one.contains(&format!("mixer at {MIXER:#x}")),
        "the mixer is not named: {one}"
    );
    assert!(
        one.contains("solve per input step with derailment as the oracle"),
        "the reading is not told how to proceed: {one}"
    );
}

/// A string built on the stack a byte at a time is recovered.
///
/// Malware keeps a string out of the data sections by writing it onto the
/// stack piece by piece; here a function spells a URL with thirteen
/// byte stores, and the recovery reads it back while a plain function offers
/// nothing.
#[test]
fn a_stack_string_is_recovered_from_its_stores() {
    let mut bytes = vec![0xccu8; 0x1000];
    bytes.extend_from_slice(&[
        0xc6, 0x44, 0x24, 0x10, 0x68, 0xc6, 0x44, 0x24, 0x11, 0x74, 0xc6, 0x44, 0x24, 0x12, 0x74,
        0xc6, 0x44, 0x24, 0x13, 0x70, 0xc6, 0x44, 0x24, 0x14, 0x3a, 0xc6, 0x44, 0x24, 0x15, 0x2f,
        0xc6, 0x44, 0x24, 0x16, 0x2f, 0xc6, 0x44, 0x24, 0x17, 0x78, 0xc6, 0x44, 0x24, 0x18, 0x2e,
        0xc6, 0x44, 0x24, 0x19, 0x69, 0xc6, 0x44, 0x24, 0x1a, 0x6f, 0xc6, 0x44, 0x24, 0x1b, 0x2f,
        0xc6, 0x44, 0x24, 0x1c, 0x61, 0xc3,
    ]);
    bytes.resize(0x2000, 0xcc);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::stack_strings_tsv(&p, &a, &o, "");
    assert!(
        text.contains("http://x.io/a"),
        "the stack string is not recovered: {text}"
    );
    let filtered = borer_engine::analysis::render::stack_strings_tsv(&p, &a, &o, "x.io");
    assert!(filtered.contains("http://x.io/a"), "{filtered}");
    assert!(
        !borer_engine::analysis::render::stack_strings_tsv(&p, &a, &o, "notthere").contains("http"),
        "the filter let everything through"
    );
    let plain = borer_engine::analysis::render::stack_strings_tsv(
        &fixture(),
        &Analysis::compute(&fixture()),
        &o,
        "",
    );
    assert!(
        plain.starts_with("# 0 ") || !plain.contains("http"),
        "{plain}"
    );
}

/// The capability map groups imports into what they let the program do.
///
/// The first question about an unknown binary is what it can do, and the
/// imports answer most of it. A program importing `WriteProcessMemory`
/// injects; one importing `SendMessageA` does not thereby talk on the
/// network, which the exact-match socket verbs ensure.
#[test]
fn the_capability_map_groups_imports() {
    let mut p = fixture();
    p.symbols = [
        "KERNEL32.dll!WriteProcessMemory",
        "USER32.dll!SendMessageA",
        "WS2_32.dll!connect",
    ]
    .iter()
    .map(|n| Symbol {
        name: (*n).to_owned(),
        addr: 0,
        kind: SymbolKind::Import,
    })
    .collect();
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(text.contains("process injection"), "{text}");
    assert!(text.contains("WriteProcessMemory"), "{text}");
    assert!(text.contains("networking"), "{text}");
    assert!(text.contains("connect"), "{text}");
    assert!(
        !text.contains("SendMessageA"),
        "a window message read as networking: {text}"
    );
}

/// The emulator runs a self-contained decoder and reads its plaintext.
///
/// A crypter puts a decoder in front of its strings: the routine carries its
/// own source pointer, length and key, reads the embedded ciphertext, and
/// writes the plaintext. Running it is the exact way to read that text with
/// no key to guess. Here a decoder at 0x1000 turns the ciphertext at 0x2000
/// into a URL at 0x2800.
#[test]
fn the_emulator_decodes_a_self_contained_string() {
    let code = [
        0x48u8, 0xb9, 0x00, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xba, 0x00, 0x20, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x4d, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x34, 0x5a,
        0x42, 0x88, 0x04, 0x11, 0x49, 0xff, 0xc2, 0x49, 0x83, 0xfa, 0x10, 0x72, 0xec, 0xc3,
    ];
    let enc = [
        0x32u8, 0x2e, 0x2e, 0x2a, 0x60, 0x75, 0x75, 0x39, 0x68, 0x74, 0x32, 0x35, 0x29, 0x2e, 0x75,
        0x22,
    ];
    let mut bytes = vec![0u8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".flat", 0, 0, 0x3000, true, true)],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::emulate_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(
        text.contains("returned"),
        "the decoder did not return: {text}"
    );
    assert!(
        text.contains("http://c2.host/x"),
        "the plaintext was not decoded: {text}"
    );
}

/// A dynamic frame does not inflate the parameter list.
///
/// A function that sizes its frame at runtime (`sub rsp, rax` after
/// `__chkstk`) hides how big the frame is, so a read of `[rsp+0x800]` is a
/// local, not the 256th stack argument. Counting it as one gave functions
/// like this thirty-odd phantom parameters; now the count declines when the
/// frame is unknown.
#[test]
fn a_dynamic_frame_does_not_invent_parameters() {
    let mut bytes = vec![0xccu8; 0x1000];
    let code = [
        0x48u8, 0x29, 0xc4, 0x8b, 0x84, 0x24, 0x00, 0x08, 0x00, 0x00, 0x31, 0xc0, 0xc3,
    ];
    bytes[0x40..0x40 + code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
    );
    p.function_ranges = vec![(0x1040, 0x104d)];
    let text = decompiled(&p, 0x1040);
    let sig = text
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .unwrap_or_default();
    let params = if sig.contains("()") {
        0
    } else {
        sig.matches(',').count() + 1
    };
    assert!(
        params <= 2,
        "a dynamic frame invented {params} parameters: {sig}"
    );
}

/// A local whose address escapes to a call is still declared.
///
/// When a function takes a local's address and passes it to a callee but
/// never reads or writes that local directly, the local has no value entry,
/// yet `&local_N` appears in the body. Declaring it keeps the text valid C.
#[test]
fn an_escaping_local_is_declared() {
    let mut bytes = vec![0xccu8; 0x1000];
    let fnb = [
        0x48u8, 0x83, 0xec, 0x38, 0x48, 0x8d, 0x4c, 0x24, 0x20, 0xe8, 0x32, 0x00, 0x00, 0x00, 0x48,
        0x83, 0xc4, 0x38, 0xc3,
    ];
    bytes[0x40..0x40 + fnb.len()].copy_from_slice(&fnb);
    bytes[0x80..0x83].copy_from_slice(&[0x8b, 0x01, 0xc3]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
    );
    p.function_ranges = vec![(0x1040, 0x1053), (0x1080, 0x1083)];
    let text = decompiled(&p, 0x1040);
    assert!(
        text.contains("&local_18"),
        "the escaping local is not used: {text}"
    );
    let declared = text.lines().any(|l| {
        l.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .any(|w| w == "local_18")
            && (l.starts_with("uint") || l.starts_with("int") || l.starts_with("char"))
    });
    assert!(
        declared,
        "the escaping local is used but never declared: {text}"
    );
}

/// The emulator resource takes arguments read from a decoder's call site.
///
/// A decoder that takes `(dst, src, len, key)` is run by naming those in the
/// target, `0x1000,rcx=0x2800,rdx=0x2000,r8=16,r9=0x5a`, the values an
/// analyst reads at the call. It XORs the ciphertext at 0x2000 into plaintext
/// at 0x2800.
#[test]
fn the_emulator_takes_call_site_arguments() {
    let code = [
        0x4du8, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x44, 0x30, 0xc8, 0x42, 0x88, 0x04, 0x11,
        0x49, 0xff, 0xc2, 0x4d, 0x39, 0xc2, 0x72, 0xec, 0xc3,
    ];
    let enc = [
        0x29u8, 0x3f, 0x39, 0x28, 0x3f, 0x2e, 0x7a, 0x2a, 0x3b, 0x23, 0x36, 0x35, 0x3b, 0x3e, 0x7b,
        0x7b,
    ];
    let mut bytes = vec![0u8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".flat", 0, 0, 0x3000, true, true)],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::emulate_tsv(
        &p,
        &a,
        &o,
        "0x1000,rcx=0x2800,rdx=0x2000,r8=0x10,r9=0x5a",
    )
    .unwrap();
    assert!(
        text.contains("secret payload!!"),
        "arguments not applied: {text}"
    );
}

/// The anti-analysis report finds the stealthy instruction tells.
///
/// A routine of `cpuid; rdtsc; sidt; in; int3` carries three strong tells a
/// compiler never emits (the descriptor-table read, the backdoor `in`, the
/// trap), so the verdict calls it out; `cpuid` and `rdtsc` alone would not.
#[test]
fn the_anti_analysis_report_finds_the_tells() {
    let mut bytes = vec![0xc3u8; 0x1000];
    let code = [
        0x0fu8, 0xa2, 0x0f, 0x31, 0x0f, 0x01, 0x0c, 0x24, 0xed, 0xcc, 0xc3,
    ];
    bytes[0x40..0x40 + code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
    );
    p.function_ranges = vec![(0x1040, 0x104b)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &o);
    assert!(
        text.starts_with("# anti-analysis:"),
        "verdict wrong: {text}"
    );
    assert!(text.contains("descriptor-table"), "{text}");
    assert!(text.contains("VMware backdoor"), "{text}");
    assert!(text.contains("debugger trap"), "{text}");
    let plain = borer_engine::analysis::render::anti_analysis_tsv(
        &fixture(),
        &Analysis::compute(&fixture()),
        &o,
    );
    assert!(
        !plain.starts_with("# anti-analysis:"),
        "plain flagged: {plain}"
    );
}

/// The check finder pins the serial routine and the value it wants.
///
/// A function that references "incorrect serial" and compares the input to
/// `0xdeadbeef` is exactly a crackme's check; the finder lists it under the
/// phrase with that constant, which is the value to forge or the branch to
/// patch.
#[test]
fn the_check_finder_pins_a_serial_routine() {
    let mut bytes = vec![0xccu8; 0x3000];
    let code = [
        0x48u8, 0x8d, 0x0d, 0xb9, 0x0f, 0x00, 0x00, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x75, 0x01, 0xc3,
        0xc3,
    ];
    bytes[0x1040..0x1040 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2011].copy_from_slice(b"incorrect serial\0");
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    );
    p.function_ranges = vec![(0x1040, 0x1050)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::license_checks_tsv(&p, &a, &o);
    assert!(
        text.contains("serial"),
        "the serial routine is not found: {text}"
    );
    assert!(
        text.contains("0xdeadbeef"),
        "the tested constant is not shown: {text}"
    );
    let plain = borer_engine::analysis::render::license_checks_tsv(
        &fixture(),
        &Analysis::compute(&fixture()),
        &o,
    );
    assert!(
        plain.starts_with("# 0 ") || !plain.contains("0xdeadbeef"),
        "{plain}"
    );
}

/// Dynamic-import recovery names an API resolved through `GetProcAddress`.
///
/// A function that calls `GetProcAddress(h, "WriteProcessMemory")` imports
/// that API without it appearing in the table; the recovery decompiles the
/// caller and lists the resolved name.
#[test]
fn dynamic_imports_name_a_resolved_api() {
    let mut bytes = vec![0xccu8; 0x3000];
    let code = [
        0x31u8, 0xc9, 0x48, 0x8d, 0x15, 0xb7, 0x0f, 0x00, 0x00, 0xff, 0x15, 0xb1, 0x17, 0x00, 0x00,
        0xc3,
    ];
    bytes[0x1040..0x1040 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2013].copy_from_slice(b"WriteProcessMemory\0");
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    );
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetProcAddress".to_owned(),
        addr: 0x2800,
        kind: SymbolKind::Import,
    }];
    p.function_ranges = vec![(0x1040, 0x1050)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::dynamic_imports_tsv(&p, &a, &o);
    assert!(
        text.contains("WriteProcessMemory"),
        "the resolved API is not recovered: {text}"
    );
}

/// The devirtualizer runs a bytecode interpreter and recovers its program.
///
/// `VM` is a real interpreter: `rsi` is the virtual instruction pointer over
/// the bytecode `[0, 1, 2, 3]`, the dispatch jumps through a table to a
/// handler per opcode, and each handler runs an operation and loops back.
/// Running it recovers the four steps as one straight-line run, `v0` to
/// `v3`, with each handler's effect, which is the virtualized function's
/// real logic.
#[test]
fn the_devirtualizer_recovers_a_virtual_program() {
    let code = [
        0x48u8, 0x8d, 0x35, 0xf9, 0x0f, 0x00, 0x00, 0x31, 0xdb, 0x0f, 0xb6, 0x06, 0x48, 0xff, 0xc6,
        0x83, 0xf8, 0x03, 0x77, 0x07, 0xff, 0x24, 0xc5, 0x00, 0x21, 0x00, 0x00, 0xc3, 0x83, 0xc3,
        0x01, 0xe9, 0xe5, 0xff, 0xff, 0xff, 0x83, 0xc3, 0x02, 0xe9, 0xdd, 0xff, 0xff, 0xff, 0x83,
        0xf3, 0x7f, 0xe9, 0xd5, 0xff, 0xff, 0xff, 0xc3,
    ];
    let mut bytes = vec![0xccu8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2004].copy_from_slice(&[0, 1, 2, 3]);
    for (i, h) in [0x101cu64, 0x1024, 0x102c, 0x1034].iter().enumerate() {
        bytes[0x2100 + i * 8..0x2100 + i * 8 + 8].copy_from_slice(&h.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    );
    p.function_ranges = vec![(0x1000, 0x1035)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::devirtualize_tsv(&p, &a, &o, "0x1000").unwrap();
    assert!(
        text.contains("4 virtual instructions"),
        "the program length is wrong: {text}"
    );
    assert!(
        text.contains("# virtual program: 4 of 4 instructions in 1 run"),
        "the program is not rendered as one run: {text}"
    );
    assert!(
        text.contains("  v0 = add;\n  v1 = add;\n  v2 = xor;"),
        "the steps are wrong: {text}"
    );
    assert!(
        text.contains("xor"),
        "the handler effects are missing: {text}"
    );
}

/// The emulator unpacks self-modifying code and recovers the hidden routine.
///
/// The stub at `0x1000` is a packer: it XOR-decrypts six bytes from `0x2000`
/// into the executable region at `0x3000`, then jumps there. On disk `0x3000`
/// holds only `int3` padding, so the hidden routine exists solely as the bytes
/// the run writes. Recovering `mov eax, 0x2a; ret` proves the emulator fetched
/// its own writes as code and that the trace found the original entry point.
#[test]
fn the_unpacker_materializes_self_modifying_code() {
    let code: [u8; 45] = [
        0x48, 0x8d, 0x35, 0xf9, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0xb9,
        0x06, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x34, 0x5a, 0x88, 0x07, 0x48, 0xff, 0xc6, 0x48,
        0xff, 0xc7, 0xff, 0xc9, 0x75, 0xef, 0x48, 0x8d, 0x05, 0xd5, 0x1f, 0x00, 0x00, 0xff, 0xe0,
    ];
    let enc: [u8; 6] = [0xe2, 0x70, 0x5a, 0x5a, 0x5a, 0x99];
    let mut bytes = vec![0xccu8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
            Section::mapped(".dest", 0x3000, 0x3000, 0x1000, true, true),
        ],
    );
    p.function_ranges = vec![(0x1000, 0x102d)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "").unwrap();
    assert!(
        text.contains("original entry point"),
        "no entry point recovered: {text}"
    );
    assert!(text.contains("0x3000"), "wrong materialized region: {text}");
    assert!(
        text.contains("mov eax,2Ah") || text.contains("mov eax,0x2a"),
        "the decrypted routine was not disassembled: {text}"
    );
    assert!(
        text.contains("entropy"),
        "the materialized region's entropy was not reported: {text}"
    );
}

/// An unpacked PE materializes into a section the file backs with no bytes.
///
/// The same packer stub, but as a PE whose destination section has a megabytes-
/// wide virtual size and zero raw bytes, the shape a protector's `.themida`
/// takes. Writing the payload back at the original file offsets would drop it,
/// since the file has no room there; rebuilding the image in memory layout
/// gives the write a home, so re-analysis discovers the routine the run
/// decrypted into `0x3000`. Before, the report carried no re-analysis at all.
#[test]
fn an_unpacked_pe_materializes_a_virtual_only_section() {
    let code: [u8; 45] = [
        0x48, 0x8d, 0x35, 0xf9, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0xb9,
        0x06, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x34, 0x5a, 0x88, 0x07, 0x48, 0xff, 0xc6, 0x48,
        0xff, 0xc7, 0xff, 0xc9, 0x75, 0xef, 0x48, 0x8d, 0x05, 0xd5, 0x1f, 0x00, 0x00, 0xff, 0xe0,
    ];
    let enc: [u8; 6] = [0xe2, 0x70, 0x5a, 0x5a, 0x5a, 0x99];
    let mut bytes = vec![0xccu8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2000 + enc.len()].copy_from_slice(&enc);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
            Section {
                file_size: 0,
                ..Section::mapped(".themida", 0x3000, 0, 0x1000, true, true)
            },
        ],
    );
    p.format = BinaryFormat::Pe;
    p.function_ranges = vec![(0x1000, 0x102d)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "").unwrap();
    assert!(
        text.contains("re-analyzed the materialized image"),
        "the virtual-only write was not rebuilt: {text}"
    );
    assert!(
        text.contains("only the materialized image has") && text.contains("0x3000"),
        "the decrypted routine was not discovered in the rebuilt image: {text}"
    );
}

/// Builds a PE-shaped image at 0x140000000 whose stub of `code_len` bytes
/// at 0x140001000 is its one declared function.
///
/// # Arguments
///
/// * `bytes` - The whole image, the stub already at file offset 0x1000.
/// * `code_len` - The stub's length in bytes.
/// * `after` - The sections after `.text`.
fn packed_pe(bytes: Vec<u8>, code_len: usize, after: Vec<Section>) -> Program {
    let mut sections = vec![Section::mapped(
        ".text",
        0x1_4000_1000,
        0x1000,
        0x1000,
        false,
        true,
    )];
    sections.extend(after);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        sections,
    );
    p.format = BinaryFormat::Pe;
    p.function_ranges = vec![(0x1_4000_1000, 0x1_4000_1000 + from_usize(code_len))];
    p
}

/// The emulator maps the PE header page the way the OS loader would.
///
/// A packer's bootstrap walks its own headers to find its imports: it reads
/// `e_lfanew` at `image_base + 0x3c`, which lies below the first section and
/// so is backed by no section's file bytes. The emulator serves it from the
/// header page at the image base, as the loader does. The stub reads that byte
/// and stores it, so a clean return with a materialized byte proves the header
/// read resolved instead of faulting.
#[test]
fn the_unpacker_maps_the_header_page() {
    let code: [u8; 17] = [
        0x0f, 0xb6, 0x05, 0x35, 0xf0, 0xff, 0xff, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0x88,
        0x07, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x3c] = 0x40;
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let p = packed_pe(
        bytes,
        code.len(),
        vec![Section::mapped(
            ".data",
            0x1_4000_3000,
            0x3000,
            0x1000,
            true,
            false,
        )],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000").unwrap();
    assert!(text.contains("returned"), "the header read faulted: {text}");
    assert!(
        text.contains("1 region"),
        "the header byte was not stored: {text}"
    );
}

/// A run that writes only data is not analyzed again; one that writes into
/// an executable section is.
///
/// The second analysis of the rebuilt image cost as much as the first, a
/// plain program's startup writes only its globals, and the code it would
/// analyze is byte for byte the original's; on borer's own build under load
/// the unpack request spent minutes there. The same store into a section
/// that is executable may be code, so that image is analyzed again.
#[test]
fn an_unpack_that_writes_only_data_is_not_analyzed_again() {
    let code: [u8; 17] = [
        0x0f, 0xb6, 0x05, 0x35, 0xf0, 0xff, 0xff, 0x48, 0x8d, 0x3d, 0xf2, 0x1f, 0x00, 0x00, 0x88,
        0x07, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x3c] = 0x40;
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    for (executable, again) in [(false, false), (true, true)] {
        let p = packed_pe(
            bytes.clone(),
            code.len(),
            vec![Section::mapped(
                ".data",
                0x1_4000_3000,
                0x3000,
                0x1000,
                true,
                executable,
            )],
        );
        let a = Analysis::compute(&p);
        let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &Overlay::default(), "")
            .expect("the stub runs");
        assert!(text.contains("1 region"), "{text}");
        assert_eq!(
            text.contains("re-analyzed the materialized image"),
            again,
            "{text}"
        );
        assert_eq!(
            text.contains(
                "# not re-analyzed: every byte the run wrote is data, outside the image's executable sections, and none of it ran"
            ),
            !again,
            "{text}"
        );
    }
}

/// The emulator services an imported call the OS loader would have resolved.
///
/// The stub calls `GetModuleHandleA` through its import-address-table slot. On
/// a static image that slot is zero, so the call would fault; the emulator
/// prefills it with a stub, recognizes the call, and models the API (a module
/// handle is the image base). The stub stores the result and returns, so a
/// clean return proves the imported call was serviced rather than followed
/// into nothing.
#[test]
fn the_unpacker_services_an_imported_call() {
    let code: [u8; 17] = [
        0xff, 0x15, 0xfa, 0x1f, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0x03, 0x20, 0x00, 0x00, 0x48, 0x89,
        0x07, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let mut p = packed_pe(
        bytes,
        code.len(),
        vec![Section::mapped(
            ".data",
            0x1_4000_3000,
            0x3000,
            0x1000,
            true,
            false,
        )],
    );
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetModuleHandleA".to_owned(),
        addr: 0x1_4000_3000,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000").unwrap();
    assert!(
        text.contains("GetModuleHandleA"),
        "the imported call was not reported: {text}"
    );
    assert!(
        text.contains("returned"),
        "the imported call faulted: {text}"
    );
}

/// The emulator runs `rep movs`, the instruction a packer copies payload with.
///
/// `cld; rep movsb` copies six bytes from a read-only source into a writable
/// region, driven by the count in `rcx`. Recovering all six bytes as a
/// materialized region proves the repeated string move ran to completion
/// rather than stopping after one step.
#[test]
fn the_unpacker_runs_a_rep_movs() {
    let code: [u8; 4] = [0xfc, 0xf3, 0xa4, 0xc3];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2006].copy_from_slice(b"ABCDEF");
    let p = packed_pe(
        bytes,
        code.len(),
        vec![
            Section::mapped(".rodata", 0x1_4000_2000, 0x2000, 0x1000, false, false),
            Section::mapped(".dest", 0x1_4000_3000, 0x3000, 0x1000, true, true),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(
        &p,
        &a,
        &o,
        "0x140001000,rcx=6,rsi=0x140002000,rdi=0x140003000",
    )
    .unwrap();
    assert!(text.contains("returned"), "the copy faulted: {text}");
    assert!(
        text.contains("0x140003000..0x140003006"),
        "the six bytes were not all copied: {text}"
    );
}

/// The emulator maps a section's page-rounded tail, as the loader does.
///
/// A section's virtual size is rarely a whole page; the loader rounds it up to
/// the page boundary and zero-fills the remainder, so a packer's decrypt loop
/// that runs to the end of a section reads mapped zeroes there rather than
/// faulting. Section `.bss` sizes `0x800` but the read at offset `0x900` lies
/// in its rounded-up page. A clean return proves the tail was mapped.
#[test]
fn the_unpacker_maps_a_page_rounded_tail() {
    let code: [u8; 5] = [0x8a, 0x06, 0x88, 0x07, 0xc3];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let p = packed_pe(
        bytes,
        code.len(),
        vec![
            Section::mapped(".bss", 0x1_4000_2000, 0x2000, 0x800, false, false),
            Section::mapped(".dest", 0x1_4000_3000, 0x3000, 0x1000, true, false),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::unpack_tsv(
        &p,
        &a,
        &o,
        "0x140001000,rsi=0x140002900,rdi=0x140003000",
    )
    .unwrap();
    assert!(
        text.contains("returned"),
        "the page-rounded tail faulted: {text}"
    );
}

/// Best-effort mode skips an unresolved import call and reaches the payload.
///
/// The stub calls through an import slot the loader would fill but a static
/// run leaves zero, then decrypts a routine and jumps to it. Best-effort is the
/// default: the call is skipped as a stub returning zero, so the decrypt runs
/// and the hidden `mov eax, 0x2a; ret` is recovered at its entry point. A
/// `strict` token faults at that call instead, pinning what the bootstrap
/// still needs.
#[test]
fn best_effort_skips_an_unresolved_call_to_reach_the_payload() {
    let code: [u8; 51] = [
        0xff, 0x15, 0xfa, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x35, 0xf3, 0x10, 0x00, 0x00, 0x48, 0x8d,
        0x3d, 0xec, 0x1f, 0x00, 0x00, 0xb9, 0x06, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x06, 0x34, 0x5a,
        0x88, 0x07, 0x48, 0xff, 0xc6, 0x48, 0xff, 0xc7, 0xff, 0xc9, 0x75, 0xef, 0x48, 0x8d, 0x05,
        0xcf, 0x1f, 0x00, 0x00, 0xff, 0xe0,
    ];
    let enc: [u8; 6] = [0xe2, 0x70, 0x5a, 0x5a, 0x5a, 0x99];
    let mut bytes = vec![0u8; 0x4000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x2100..0x2106].copy_from_slice(&enc);
    let p = packed_pe(
        bytes,
        code.len(),
        vec![
            Section::mapped(".rdata", 0x1_4000_2000, 0x2000, 0x1000, false, false),
            Section::mapped(".dest", 0x1_4000_3000, 0x3000, 0x1000, true, true),
        ],
    );
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let best = borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000").unwrap();
    assert!(
        best.contains("skipped"),
        "the skip was not reported: {best}"
    );
    assert!(
        best.contains("original entry point"),
        "best-effort did not reach the payload: {best}"
    );
    assert!(
        best.contains("mov eax,2Ah") || best.contains("mov eax,0x2a"),
        "the decrypted routine was not recovered: {best}"
    );
    let strict =
        borer_engine::analysis::render::unpack_tsv(&p, &a, &o, "0x140001000,strict").unwrap();
    assert!(
        !strict.contains("original entry point"),
        "strict mode should stop at the unresolved call: {strict}"
    );
}

/// The binary diff finds what an update changed, added and removed.
///
/// Two builds hold `funcA` (identical code, moved to a new address), `funcB`
/// (same name, a changed constant), `funcD` (dropped in the new build) and
/// `funcC` (new in it). The diff must read one unchanged, one changed, one
/// added and one removed, proving it matches on the address-independent body
/// fingerprint rather than on where the code sits.
#[test]
fn the_diff_reports_what_changed_between_versions() {
    fn mk(text_va: u64, items: &[(u64, &[u8], &str)]) -> Program {
        let top = items
            .iter()
            .map(|(va, b, _)| va + b.len() as u64)
            .max()
            .unwrap_or(text_va);
        let mut bytes = vec![0u8; usize::try_from(top + 0x1000).expect("fits")];
        let mut symbols = Vec::new();
        let mut ranges = Vec::new();
        for (va, b, name) in items {
            let at = usize::try_from(*va).expect("fits");
            bytes[at..at + b.len()].copy_from_slice(b);
            symbols.push(Symbol {
                name: (*name).to_owned(),
                addr: *va,
                kind: SymbolKind::Local,
            });
            ranges.push((*va, va + b.len() as u64));
        }
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            None,
            vec![Section::mapped(
                ".text",
                text_va,
                text_va,
                top + 0x1000 - text_va,
                false,
                true,
            )],
        );
        p.format = BinaryFormat::Pe;
        p.symbols = symbols;
        p.function_ranges = ranges;
        p
    }
    let ret = 0xc3u8;
    let old = mk(
        0x1000,
        &[
            (0x1000, &[0x31, 0xc0, ret], "funcA"),
            (0x1040, &[0xb8, 0x01, 0x00, 0x00, 0x00, ret], "funcB"),
            (0x1080, &[0xb9, 0x09, 0x00, 0x00, 0x00, ret], "funcD"),
        ],
    );
    let new = mk(
        0x2000,
        &[
            (0x2000, &[0x31, 0xc0, ret], "funcA"),
            (0x2040, &[0xb8, 0x02, 0x00, 0x00, 0x00, ret], "funcB"),
            (0x2080, &[0x83, 0xc0, 0x05, ret], "funcC"),
        ],
    );
    let oa = Analysis::compute(&old);
    let na = Analysis::compute(&new);
    let text = borer_engine::analysis::render::diff_tsv(&oa, &na, "old.exe", "new.exe");
    assert!(
        text.contains("unchanged 1, changed 1, added 1, removed 1"),
        "the diff counts are wrong: {text}"
    );
    assert!(
        text.contains("funcB"),
        "the changed function is missing: {text}"
    );
    assert!(
        text.contains("funcC"),
        "the added function is missing: {text}"
    );
    assert!(
        text.contains("funcD"),
        "the removed function is missing: {text}"
    );
}

/// The per-function diff shows how a changed function changed, in its C.
///
/// Both builds hold `check`, which compares a field against a constant; the
/// constant changed between them. The decompilation diff must drop the line
/// with the old constant and add the line with the new one, which is the edit
/// a reverser wants to see, not merely that the function differs.
#[test]
fn the_per_function_diff_shows_the_changed_line() {
    fn mk(va: u64, cmp: &[u8]) -> Program {
        let mut code = vec![0x8b, 0x01];
        code.extend_from_slice(cmp);
        code.extend_from_slice(&[0x0f, 0x94, 0xc0, 0xc3]);
        let mut bytes = vec![0u8; usize::try_from(va + 0x100).expect("fits") + code.len()];
        let at = usize::try_from(va).expect("fits");
        bytes[at..at + code.len()].copy_from_slice(&code);
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            None,
            vec![Section::mapped(".text", va, va, 0x1000, false, true)],
        );
        p.format = BinaryFormat::Pe;
        p.symbols = vec![Symbol {
            name: "check".to_owned(),
            addr: va,
            kind: SymbolKind::Local,
        }];
        p.function_ranges = vec![(va, va + code.len() as u64)];
        p
    }
    let old = mk(0x1000, &[0x3d, 0xef, 0xbe, 0xad, 0xde]);
    let new = mk(0x2000, &[0x3d, 0xbe, 0xba, 0xfe, 0xca]);
    let oa = Analysis::compute(&old);
    let na = Analysis::compute(&new);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::diff_function_tsv(
        &old, &oa, &o, &new, &na, &o, "check", "old", "new",
    )
    .expect("check is a baseline function");
    assert!(
        text.contains("0xdeadbeef"),
        "the old constant is missing: {text}"
    );
    assert!(
        text.contains("0xcafebabe"),
        "the new constant is missing: {text}"
    );
    assert!(
        !text.contains("identical body"),
        "a real change read as identical: {text}"
    );
}

/// A saved fingerprint manifest round-trips and drives a diff without the old
/// binary, so "what changed since last scan" needs only the new file.
///
/// The baseline's manifest is rendered, parsed back, and used as the old side
/// of a diff: against the same build it reads identical, and against a build
/// whose `funcB` constant changed it reports the one changed function. That is
/// the sidecar workflow, the prior version carried as a small text file.
#[test]
fn the_fingerprint_manifest_drives_a_diff() {
    fn mk(b_const: &[u8]) -> Program {
        let a_code = [0x31u8, 0xc0, 0xc3];
        let mut b_code = vec![0xb8u8];
        b_code.extend_from_slice(b_const);
        b_code.push(0xc3);
        let mut bytes = vec![0u8; 0x2000];
        bytes[0x1000..0x1000 + a_code.len()].copy_from_slice(&a_code);
        bytes[0x1040..0x1040 + b_code.len()].copy_from_slice(&b_code);
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            None,
            vec![Section::mapped(
                ".text", 0x1000, 0x1000, 0x1000, false, true,
            )],
        );
        p.format = BinaryFormat::Pe;
        p.symbols = vec![
            Symbol {
                name: "funcA".to_owned(),
                addr: 0x1000,
                kind: SymbolKind::Local,
            },
            Symbol {
                name: "funcB".to_owned(),
                addr: 0x1040,
                kind: SymbolKind::Local,
            },
        ];
        p.function_ranges = vec![(0x1000, 0x1003), (0x1040, 0x1046)];
        p
    }
    use borer_engine::analysis::render;
    let old = mk(&[0xef, 0xbe, 0xad, 0xde]);
    let new = mk(&[0xbe, 0xba, 0xfe, 0xca]);
    let oa = Analysis::compute(&old);
    let na = Analysis::compute(&new);
    let manifest = render::fingerprint_tsv(&oa);
    let parsed = render::parse_prints(&manifest);
    assert_eq!(
        parsed.len(),
        oa.functions.len(),
        "manifest lost functions: {manifest}"
    );
    let same = render::diff_prints_tsv(&parsed, &render::prints_of(&oa), "old.bfp", "old.exe");
    assert!(
        same.contains("identical"),
        "round-trip was not identical: {same}"
    );
    let changed = render::diff_prints_tsv(&parsed, &render::prints_of(&na), "old.bfp", "new.exe");
    assert!(
        changed.contains("changed 1"),
        "the change was not found: {changed}"
    );
    assert!(
        !changed.contains("identical"),
        "a real change read as identical: {changed}"
    );
}

/// A function behind padding is found even inside another's range.
///
/// `HD` sits in the gap between `HG`'s two blocks, which is where a linker
/// puts the small accessors a class emits; nothing calls it and no pointer
/// names it, so only the padding before it says it exists. Asking whether
/// some function's range reaches over it, rather than whether a block
/// covers it, hides every function in such a gap.
#[test]
fn a_function_in_a_gap_between_blocks_is_still_found() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let hd = a.function(0x51d0).expect("the function behind the padding");
    assert_eq!(hd.entry, 0x51d0);
    assert_eq!(
        a.function(0x51c0).map(|f| f.blocks.len()),
        Some(3),
        "the function it sits inside keeps its own blocks"
    );
}

/// The width callers read of a result is recorded on the callee.
///
/// `BL`'s only caller `CW` tests `al`, so it returns a byte; `Q`'s callers
/// read `eax` and wider, and its bare `ret` writes nothing narrower.
#[test]
fn callers_read_width_is_recorded_on_the_callee() {
    let a = Analysis::compute(&fixture());
    assert_eq!(a.function(0x1f30).and_then(|f| f.ret_width), Some(8));
    let q = a.function(0x11e0).and_then(|f| f.ret_width);
    assert!(q.is_none(), "{q:?}");
}

/// A function whose every return follows a byte write of rax returns a byte,
/// however wide its callers read it.
///
/// `BB` ends `sete al; ret` while its caller `CB2` copies `eax` whole, so
/// the body decides: `BB` returns a byte.
#[test]
fn byte_writes_before_every_return_narrow_the_result() {
    let a = Analysis::compute(&fixture());
    assert_eq!(a.function(0x1f60).and_then(|f| f.ret_width), Some(8));
}

/// A whole-register write whose value fits a byte counts as a byte write.
///
/// `BZ` returns `movzx eax, byte [rcx+0x10]`: the write fills `eax`, but
/// the value fits a byte, and its caller `CZ` copies `eax` whole, so the
/// body decides: `BZ` returns a byte.
#[test]
fn values_that_fit_a_byte_narrow_the_result() {
    let a = Analysis::compute(&fixture());
    assert_eq!(a.function(0x1f90).and_then(|f| f.ret_width), Some(8));
}

/// A return reached only when rax is zero hands back a byte.
///
/// `BN` loads a pointer into `rax` and returns it as is when it is null
/// (`test rax, rax; jz Z; ... Z: ret`), else a zero-extended byte; the
/// null path returns zero, which fits a byte, so `BN` returns a byte.
#[test]
fn returns_entered_only_on_zero_narrow_the_result() {
    let a = Analysis::compute(&fixture());
    assert_eq!(a.function(0x1fc0).and_then(|f| f.ret_width), Some(8));
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

/// An entry-address filter matches with or without its `0x` prefix.
///
/// Every other address parameter takes `0x`, so a filter that silently finds
/// nothing for `0x1230` and one row for `1230` costs a wasted round trip.
#[test]
fn function_filters_accept_an_0x_prefixed_address() {
    let a = Analysis::compute(&fixture());
    let o = Overlay::default();
    use borer_engine::analysis::render::{FunctionOrder, functions_tsv};
    let bare = functions_tsv(&a, &o, Some("1230"), FunctionOrder::Address, 0, 50);
    let prefixed = functions_tsv(&a, &o, Some("0x1230"), FunctionOrder::Address, 0, 50);
    assert_eq!(bare.2, prefixed.2);
    assert!(prefixed.2.contains("0x1230"), "{}", prefixed.2);
}

/// A call or jump through an import slot is a call or a jump, not a data read.
///
/// `call qword [rel <IAT slot>]` is how a PE reaches an import without a
/// thunk. Recording the slot as a plain memory reference hides every such
/// call: the import's cross-references read `imm/mem`, and no caller lists
/// the import among its callees.
#[test]
fn calls_through_an_import_slot_keep_their_kind() {
    let a = Analysis::compute(&fixture());
    let sites = a
        .xrefs
        .get(&0x2050)
        .expect("ReportAssertFailure slot has refs");
    let kind_at = |va: u64| sites.iter().find(|s| s.va == va).map(|s| s.kind);
    assert_eq!(kind_at(0x1230), Some(RefKind::Call), "{sites:?}");
    assert_eq!(kind_at(0x1210), Some(RefKind::Jmp), "{sites:?}");
}

/// The cross-reference listing spells each site's kind as the word it
/// always printed, so a typed kind changes no answer.
#[test]
fn an_xrefs_row_spells_each_site_kind() {
    let a = Analysis::compute(&fixture());
    let out =
        borer_engine::analysis::render::xrefs_tsv(&a, &Overlay::default(), 0x2050, 0, 60, false);
    assert!(out.contains("0x1230 call"), "{out}");
    assert!(out.contains("0x1210 jmp"), "{out}");
}

/// `why` names an import's IAT slot by the import, as `symbols` lists it.
///
/// Asked by the slot's address or by the name of an import called straight
/// through its slot, it said "nothing names it" while the symbol index held
/// exports and locals alone. An export at an address still wins.
#[test]
fn why_names_an_import_slot() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let slot = a.symbol_at(&p, 0x2050).expect("the slot has a symbol");
    assert_eq!(
        (slot.name.as_str(), slot.kind),
        ("KERNEL32.dll!ReportAssertFailure", SymbolKind::Import)
    );
    assert_eq!(
        a.symbol_at(&p, 0x1040).map(|s| s.name.as_str()),
        Some("exported_c")
    );
    for (target, import) in [
        ("0x2050", "ReportAssertFailure"),
        ("ExitProcess", "ExitProcess"),
    ] {
        let out =
            borer_engine::analysis::render::why_tsv(&p, &a, &o, target).expect("the slot resolves");
        assert!(
            out.contains(&format!(
                "# name: the import symbol table: KERNEL32.dll!{import}"
            )),
            "{target}: {out}"
        );
    }
}

/// An export is a reason a function was discovered, and `why` gives it:
/// the image's exports seed discovery, and the answer left them out.
#[test]
fn why_counts_an_export_among_the_discovery_reasons() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let out = borer_engine::analysis::render::why_tsv(&p, &a, &Overlay::default(), "0x1040")
        .expect("the export resolves");
    let how = out
        .lines()
        .find(|l| l.starts_with("# discovered by: "))
        .unwrap_or_default();
    assert!(how.contains("an export"), "{out}");
}

/// A summary lists the imports its function calls straight through the slot.
#[test]
fn summary_callees_name_a_directly_called_import() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let out = borer_engine::analysis::render::function_summary(&p, &a, &Overlay::default(), 0x1230)
        .expect("summary");
    assert!(out.contains("KERNEL32.dll!ReportAssertFailure"), "{out}");
}

/// A function's size counts the bytes of its blocks, not the span it covers.
///
/// A tail jump into a distant thunk absorbs that block, so `end - start`
/// reports the distance to it: on a real PE a two-instruction import thunk
/// measured 832,414 bytes that way, a quarter of the image, and the jump
/// tables of every function inside the span were attributed to it.
#[test]
fn function_size_counts_block_bytes_not_span() {
    let a = Analysis::compute(&fixture());
    for f in &a.functions {
        let blocks: u64 = f.blocks.iter().map(|b| b.end.saturating_sub(b.start)).sum();
        assert_eq!(
            f.size(),
            blocks,
            "{:#x} size is not its block bytes",
            f.entry
        );
        assert!(
            f.size() <= f.end.saturating_sub(f.start),
            "{:#x} size exceeds its span",
            f.entry
        );
    }
}

/// The next free addresses sit above every span the image writes.
///
/// The guard that keeps parallel fixture authors from claiming one span
/// twice: an overlap panics at the build, and the free addresses stay
/// above the claims.
#[test]
fn the_fixture_allocates_from_free_addresses() {
    fixture();
    let code = common::next_free("code");
    assert!(
        code > 0x5880,
        "code free address {code:#x} sits inside claims"
    );
    let data = common::next_free("data");
    assert!(
        data > 0x37f0,
        "data free address {data:#x} sits inside claims"
    );
}

/// Every fixture function is discovered, in address order, with fuel to spare.
#[test]
fn discovers_all_fixture_functions() {
    let a = Analysis::compute(&fixture());
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert_eq!(
        entries,
        vec![
            0x1000, 0x1020, 0x1030, 0x1040, 0x1050, 0x1060, 0x10e0, 0x10e1, 0x1100, 0x1118, 0x1130,
            0x1150, 0x1160, 0x1180, 0x11a0, 0x11c0, 0x11e0, 0x11e4, 0x1200, 0x1210, 0x1220, 0x1230,
            0x1240, 0x1250, 0x1270, 0x127b, 0x1290, 0x12b0, 0x12c0, 0x12ca, 0x12d0, 0x12e0, 0x12f0,
            0x1300, 0x1320, 0x1340, 0x1360, 0x1380, 0x13a0, 0x13b0, 0x13c0, 0x13d0, 0x13f0, 0x1400,
            0x1410, 0x1430, 0x1450, 0x1470, 0x1490, 0x14b0, 0x14d0, 0x14f0, 0x1510, 0x1520, 0x1530,
            0x1550, 0x1590, 0x15b0, 0x15d0, 0x15e0, 0x1600, 0x1610, 0x1620, 0x1630, 0x1640, 0x1660,
            0x1670, 0x1680, 0x1690, 0x16b0, 0x16c0, 0x16d0, 0x16f0, 0x1710, 0x1730, 0x1740, 0x1750,
            0x1770, 0x1780, 0x17a0, 0x17b0, 0x17d0, 0x17f0, 0x1800, 0x1810, 0x1840, 0x1870, 0x1880,
            0x1890, 0x18a0, 0x18b0, 0x18c0, 0x18d0, 0x18e0, 0x18f0, 0x1920, 0x1950, 0x1960, 0x1980,
            0x1990, 0x19a0, 0x19d0, 0x19e0, 0x1a00, 0x1a30, 0x1a40, 0x1a50, 0x1a60, 0x1a90, 0x1ab0,
            0x1ad0, 0x1ae0, 0x1b00, 0x1b10, 0x1b20, 0x1b30, 0x1b40, 0x1b50, 0x1b80, 0x1b90, 0x1ba0,
            0x1bb0, 0x1bc0, 0x1bd0, 0x1be0, 0x1bf0, 0x1c00, 0x1c10, 0x1c20, 0x1c30, 0x1c50, 0x1c60,
            0x1c80, 0x1cb0, 0x1cf0, 0x1d30, 0x1d90, 0x1dd0, 0x1de0, 0x1df0, 0x1e00, 0x1e10, 0x1e30,
            0x1e40, 0x1e50, 0x1e70, 0x1eb0, 0x1ed0, 0x1ee0, 0x1f00, 0x1f30, 0x1f40, 0x1f60, 0x1f70,
            0x1f90, 0x1fa0, 0x1fc0, 0x1fd0, 0x1fe4, 0x4000, 0x4041, 0x4050, 0x4090, 0x40f4, 0x4100,
            0x4120, 0x4130, 0x4150, 0x4160, 0x4170, 0x4180, 0x41d0, 0x41e0, 0x4200, 0x4210, 0x4220,
            0x4240, 0x4260, 0x4300, 0x4790, 0x47a0, 0x47b0, 0x4830, 0x4870, 0x48d0, 0x4900, 0x4930,
            0x4990, 0x49a0, 0x49b0, 0x4a20, 0x4a40, 0x4a50, 0x4aa0, 0x4ac0, 0x4ae0, 0x4b00, 0x4b10,
            0x4b20, 0x4b30, 0x4b40, 0x4b60, 0x4b90, 0x4bb0, 0x4bc0, 0x4be0, 0x4bf0, 0x4c00, 0x4c10,
            0x4c20, 0x4c30, 0x4c40, 0x4c60, 0x4c90, 0x4cb0, 0x4ce0, 0x4d20, 0x4d50, 0x4d70, 0x4d80,
            0x4d90, 0x4da0, 0x4dc0, 0x4de0, 0x4e00, 0x4e20, 0x4e50, 0x4e80, 0x4e90, 0x4eb0, 0x4ec0,
            0x4ed0, 0x4ee0, 0x4f00, 0x4f20, 0x4f60, 0x4f70, 0x4f90, 0x4fb0, 0x4fd0, 0x5000, 0x5040,
            0x5080, 0x50a0, 0x50b0, 0x50c0, 0x5130, 0x5150, 0x5170, 0x5190, 0x51c0, 0x51d0, 0x5200,
            0x5240, 0x52a0, 0x52c0, 0x5300, 0x5306, 0x530c, 0x5312, 0x5320, 0x5360, 0x5366, 0x536c,
            0x5372, 0x5378, 0x5390, 0x5445, 0x5450, 0x54cd, 0x54e0, 0x5500, 0x553f, 0x5550, 0x5560,
            0x5570, 0x5580, 0x5590, 0x55c0, 0x55e0, 0x5600, 0x5620, 0x5630, 0x5640, 0x5650, 0x5660,
            0x5680, 0x56a0, 0x56b0, 0x56c0, 0x5700, 0x5720, 0x5730, 0x5740, 0x5750, 0x5760, 0x57a0,
            0x57c0, 0x57c6, 0x57e0, 0x5800, 0x5830, 0x5850, 0x5870, 0x5876, 0x587c, 0x5882, 0x5900,
            0x5910, 0x5930, 0x5c00, 0x5c40,
        ]
    );
    assert!(!a.incomplete);
}

/// `W` is walked before `main` reveals that `A` is a function; the re-walk
/// turns its `jmp A` into a tail call instead of absorbing `A`'s body.
#[test]
fn tail_jump_into_a_function_is_a_call() {
    let a = Analysis::compute(&fixture());
    let w = a.function(0x1240).unwrap();
    assert_eq!(w.end, 0x124a, "W absorbed A: {w:?}");
    assert_eq!(w.instr_count, 2);
    assert_eq!(w.callees, vec![0x1020]);
    assert!(a.function(0x1020).unwrap().callers.contains(&0x1240));
    let sites = a.xrefs_to(0x1020);
    assert!(
        sites
            .iter()
            .any(|s| s.va == 0x1245 && s.kind == RefKind::Jmp),
        "{sites:?}"
    );
}

/// `E` at 0x10e0 is reachable only through the qword pointer at 0x2030 and is
/// still discovered (phase 2, pointer seeds).
#[test]
fn pointer_seeded_function_found() {
    let a = Analysis::compute(&fixture());
    let e = a
        .function(0x10e0)
        .expect("pointer-referenced function must be discovered");
    assert_eq!(e.entry, 0x10e0);
}

/// The switch at 0x1071 resolves its four-entry table, and the case bodies
/// belong to the switch function rather than becoming functions of their own.
#[test]
fn jump_table_resolved() {
    let a = Analysis::compute(&fixture());
    let targets = a
        .jump_tables
        .get(&0x1071)
        .expect("switch at 0x1071 must resolve its table");
    assert_eq!(targets, &vec![0x1090, 0x10a0, 0x10b0, 0x10c0]);
    assert_eq!(a.function_at(0x1090).unwrap().entry, 0x1060);
    assert_eq!(a.function_at(0x10b0).unwrap().entry, 0x1060);
}

/// `main` splits into four blocks (a call ends its block):
/// `0x1000 call | 0x1005 test+jz | 0x1009 call | 0x100e xor+ret`, with the
/// expected terminators, successors, counts and range.
#[test]
fn main_blocks_and_terminators() {
    let a = Analysis::compute(&fixture());
    let main = a.function(0x1000).unwrap();
    let starts: Vec<u64> = main.blocks.iter().map(|b| b.start).collect();
    assert_eq!(starts, vec![0x1000, 0x1005, 0x1009, 0x100e]);

    assert_eq!(main.blocks[0].term.name(), "call");
    assert_eq!(main.blocks[0].successors, vec![0x1005]);

    let b1 = &main.blocks[1];
    assert_eq!(b1.term.name(), "cond");
    let mut succ: Vec<u64> = b1.successors.clone();
    succ.sort_unstable();
    assert_eq!(succ, vec![0x1009, 0x100e]);

    assert_eq!(main.blocks[2].term.name(), "call");
    assert_eq!(main.blocks[2].successors, vec![0x100e]);
    assert_eq!(main.blocks[3].term.name(), "ret");
    assert!(main.blocks[3].successors.is_empty());
    assert_eq!(main.instr_count, 6);
    assert_eq!(main.start, 0x1000);
    assert_eq!(main.end, 0x1011);
}

/// Callee and caller lists are filled in both directions (a tail call counts
/// as a call); exported functions carry their symbol name and unnamed ones
/// carry none.
#[test]
fn call_edges_and_names() {
    let a = Analysis::compute(&fixture());
    let main = a.function(0x1000).unwrap();
    assert_eq!(main.callees, vec![0x1020, 0x1030]);
    assert_eq!(a.function(0x1020).unwrap().callers, vec![0x1000, 0x1240]);
    assert_eq!(a.function(0x1030).unwrap().callers, vec![0x1000]);
    assert_eq!(
        a.function(0x1040).unwrap().name.as_deref(),
        Some("exported_c")
    );
    assert!(a.function(0x1000).unwrap().name.is_none());
}

/// `function_at` maps interior addresses (including switch case bodies) to
/// their function and returns `None` in the gap between `D` and `E`.
#[test]
fn function_at_containing_range() {
    let a = Analysis::compute(&fixture());
    assert_eq!(a.function_at(0x1003).unwrap().entry, 0x1000);
    assert_eq!(a.function_at(0x1044).unwrap().entry, 0x1040);
    assert_eq!(a.function_at(0x1099).unwrap().entry, 0x1060);
    assert!(a.function_at(0x10d0).is_none());
}

/// Call and tail-jump sites are recorded as code cross-references with
/// their containing function.
#[test]
fn code_xrefs() {
    let a = Analysis::compute(&fixture());
    let to_a = a.xrefs_to(0x1020);
    assert_eq!(to_a.len(), 2);
    assert_eq!((to_a[0].va, to_a[0].kind), (0x1000, RefKind::Call));
    assert_eq!(to_a[0].from_entry, Some(0x1000));
    assert_eq!((to_a[1].va, to_a[1].kind), (0x1245, RefKind::Jmp));
    assert_eq!(to_a[1].from_entry, Some(0x1240));
    let to_b = a.xrefs_to(0x1030);
    assert_eq!(to_b[0].va, 0x1009);
}

/// A rip-relative memory operand is recorded as an `imm/mem` data reference.
#[test]
fn rip_relative_data_xref() {
    let a = Analysis::compute(&fixture());
    let sites = a.xrefs_to(0x2007);
    assert_eq!(sites.len(), 1);
    assert_eq!(sites[0].va, 0x1040);
    assert_eq!(sites[0].kind, RefKind::Data);
}

/// Name resolution order: overlay name, then symbol, then `sub_<addr>`.
#[test]
fn overlay_names_win() {
    let a = Analysis::compute(&fixture());
    let mut o = Overlay::default();
    o.names.insert(0x1000, "main".to_owned());
    assert_eq!(name_of(&a, &o, 0x1000), "main");
    assert_eq!(name_of(&a, &o, 0x1040), "exported_c");
    assert_eq!(name_of(&a, &o, 0x1020), "sub_1020");
    let empty = Overlay {
        names: BTreeMap::new(),
        comments: BTreeMap::new(),
        ..Overlay::default()
    };
    assert_eq!(name_of(&a, &empty, 0x1020), "sub_1020");
}

/// An import thunk (`jmp [IAT]`) takes the import's name and is a callee of its caller.
#[test]
fn import_thunk_takes_the_import_name() {
    let a = Analysis::compute(&fixture());
    let t = a
        .function(0x1210)
        .expect("thunk discovered via pointer seed");
    assert_eq!(t.name.as_deref(), Some("KERNEL32.dll!ReportAssertFailure"));
    assert_eq!(a.function(0x1220).unwrap().callees, vec![0x1210]);
}

/// `resolve` accepts hex, decimal, symbol, overlay and `sub_` names.
///
/// Symbol names match case-insensitively. An import with a thunk resolves to
/// the thunk, with or without its DLL prefix, while the IAT slot stays
/// reachable by address.
#[test]
fn resolve_names_and_addresses() {
    use borer_engine::analysis::resolve;
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1000, "main".to_owned());
    assert_eq!(resolve(&p, &a, &o, "0x1040"), Ok(0x1040));
    assert_eq!(resolve(&p, &a, &o, "4160"), Ok(4160));
    assert_eq!(resolve(&p, &a, &o, "exported_c"), Ok(0x1040));
    assert_eq!(resolve(&p, &a, &o, "EXPORTED_C"), Ok(0x1040));
    assert_eq!(resolve(&p, &a, &o, "main"), Ok(0x1000));
    assert_eq!(resolve(&p, &a, &o, "sub_1020"), Ok(0x1020));
    assert_eq!(resolve(&p, &a, &o, "ReportAssertFailure"), Ok(0x1210));
    assert_eq!(
        resolve(&p, &a, &o, "KERNEL32.dll!ReportAssertFailure"),
        Ok(0x1210)
    );
    assert!(resolve(&p, &a, &o, "no_such_thing").is_err());
}

/// A name nothing matches is answered with the names nearest it when an
/// agent asked (`resolve_suggesting`).
///
/// A near spelling finds the name, and a part of a thunk's name finds it
/// without its DLL; plain `resolve` stays without the search, and a word
/// nothing resembles gets no list.
///
/// # Panics
///
/// When a miss names the wrong names, or a hit or a plain miss changed.
#[test]
fn a_missed_name_suggests_the_nearest_names() {
    use borer_engine::analysis::{resolve, resolve_suggesting};
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1000, "check_serial".to_owned());
    let miss = resolve_suggesting(&p, &a, &o, "chk_serial").unwrap_err();
    assert!(
        miss.starts_with("'chk_serial' is neither an address nor a known name; nearest: check_serial; try functions(filter=...)"),
        "{miss}"
    );
    let part = resolve_suggesting(&p, &a, &o, "ReportAssert").unwrap_err();
    assert!(part.contains("; nearest: ReportAssertFailure; "), "{part}");
    let plain = resolve(&p, &a, &o, "chk_serial").unwrap_err();
    assert!(!plain.contains("nearest"), "{plain}");
    let far = resolve_suggesting(&p, &a, &o, "zzzzqqqq").unwrap_err();
    assert!(!far.contains("nearest"), "{far}");
    assert_eq!(resolve_suggesting(&p, &a, &o, "check_serial"), Ok(0x1000));
}

/// Asking for the function at an import's slot is answered with what the
/// slot is: the import's code lives in another module.
///
/// # Panics
///
/// When the slot reads as a function not found, or the function in the
/// image is not found.
#[test]
fn an_import_slot_is_no_function_and_says_so() {
    use borer_engine::analysis::function_entry;
    let mut bytes = vec![0u8; 0x2000];
    bytes[0] = 0xc3; // ASM: ret
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![
            Section::mapped(".text", 0x1_4000_1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x1_4000_2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Pe;
    p.symbols.push(Symbol {
        name: "KERNEL32.dll!GetLastError".to_owned(),
        addr: 0x1_4000_2000,
        kind: SymbolKind::Import,
    });
    let a = Analysis::compute(&p);
    assert_eq!(function_entry(&p, &a, 0x1_4000_1000), Ok(0x1_4000_1000));
    let err = function_entry(&p, &a, 0x1_4000_2000).unwrap_err();
    assert!(
        err.contains("import slot of KERNEL32.dll!GetLastError"),
        "{err}"
    );
    let err = function_entry(&p, &a, 0x1_4000_2100).unwrap_err();
    assert!(err.contains("no discovered function contains"), "{err}");
}

/// A name that spells a number resolves to what it names; `0x` text is
/// always the address, and text no name matches reads as a number.
///
/// `add`, `cafe` and `1234` read as hex or decimal before any name was
/// looked up, so a function given one of them could not be reached by it.
#[test]
fn a_name_that_reads_as_a_number_resolves_by_name() {
    use borer_engine::analysis::resolve;
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1000, "cafe".to_owned());
    o.names.insert(0x1020, "1234".to_owned());
    assert_eq!(resolve(&p, &a, &o, "cafe"), Ok(0x1000));
    assert_eq!(resolve(&p, &a, &o, "CAFE"), Ok(0x1000));
    assert_eq!(resolve(&p, &a, &o, "1234"), Ok(0x1020));
    assert_eq!(resolve(&p, &a, &o, "0xcafe"), Ok(0xcafe));
    assert_eq!(resolve(&p, &a, &o, "0x1234"), Ok(0x1234));
    assert_eq!(resolve(&p, &a, &o, "4160"), Ok(4160));
    assert_eq!(resolve(&p, &a, &o, "f00d"), Ok(0xf00d));
}

/// A call to a noreturn import ends the path: `Y` stops at its call to
/// `ExitProcess` and `Z`, which starts right after it, stays a function of its own.
#[test]
fn call_to_noreturn_import_ends_the_function() {
    let a = Analysis::compute(&fixture());
    let y = a.function(0x1270).unwrap();
    assert_eq!(y.end, 0x127b, "Y absorbed Z: {y:?}");
    assert_eq!(y.instr_count, 2);
    assert_eq!(a.function(0x127b).unwrap().instr_count, 2);
}

/// `NR` has no name; `Y3` calls it with `Z3` starting right after the call, so
/// it is discovered to never return, and `W3` (walked earlier) is re-walked and
/// loses its dead tail.
#[test]
fn discovered_noreturn_callee_cuts_every_caller() {
    let a = Analysis::compute(&fixture());
    let y3 = a.function(0x12c0).unwrap();
    assert_eq!(y3.end, 0x12ca, "Y3 absorbed Z3: {y3:?}");
    let w3 = a.function(0x12d0).unwrap();
    assert_eq!(w3.end, 0x12da, "W3 kept its dead tail: {w3:?}");
    assert_eq!(w3.instr_count, 2);
    assert_eq!(a.function(0x12b0).unwrap().callers, vec![0x12c0, 0x12d0]);
}

/// `S` references the string at 0x2040 and calls `Q`: the summary, the
/// function-strings table and the by-string lookup all show it, and `U`'s
/// summary names the import through the thunk.
#[test]
fn refs_from_and_summary() {
    use borer_engine::analysis::render::{
        function_strings_tsv, function_summary, functions_by_string_tsv, xrefs_tsv,
    };
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let refs = a.refs_from(0x1200);
    assert!(
        refs.iter().any(|(t, _)| *t == 0x2040),
        "string ref missing: {refs:?}"
    );
    let summary = function_summary(&p, &a, &o, 0x1200).unwrap();
    assert!(summary.contains("callees:  1 [Base::vfunc_1]"), "{summary}");
    assert!(summary.contains("\"hello, borer world\""), "{summary}");
    let strings = function_strings_tsv(&p, &a, &o, 0x1200).unwrap();
    assert!(strings.contains("0x2040"), "{strings}");
    let refs = xrefs_tsv(&a, &o, 0x2040, 0, 60, false);
    assert!(
        refs.contains("(+1 function running the same code)"),
        "the registration pair was listed twice: {refs}"
    );
    assert!(refs.contains("# 4 xrefs to 0x2040"), "{refs}");
    let alone = refs
        .lines()
        .find(|l| l.contains("exported_s"))
        .unwrap_or_default();
    assert!(
        !alone.contains("running the same code"),
        "a lone referrer was collapsed: {refs}"
    );
    let by_string = functions_by_string_tsv(&p, &a, &o, "BORER", 0, 10);
    assert!(by_string.contains("exported_s"), "{by_string}");
    assert!(
        by_string.contains("across 1 string in 4 functions\n"),
        "plural: {by_string}"
    );
    assert!(
        by_string.contains("# strings: 1=\"hello, borer world\"\n"),
        "{by_string}"
    );
    assert!(by_string.contains("exported_x: 1\n"), "{by_string}");
    assert!(
        by_string.contains("(+1 function running the same code)"),
        "the registration pair was listed twice: {by_string}"
    );
    let u = function_summary(&p, &a, &o, 0x1220).unwrap();
    assert!(u.contains("KERNEL32.dll!ReportAssertFailure"), "{u}");
    let chk = function_summary(&p, &a, &o, 0x1810).unwrap();
    assert!(chk.contains("source:   util/fourcc.h\n"), "{chk}");
    assert!(chk.contains("asserts:  f.IsValid()"), "{chk}");
    let pt = function_summary(&p, &a, &o, 0x4fd0).unwrap();
    assert!(
        pt.contains(
            "passed:   a1 = 7, 9
"
        ),
        "{pt}"
    );
    let with_pack = Analysis::compute_with(&p, fixture_pack());
    let ec = function_summary(&p, &with_pack, &o, 0x50c0).unwrap();
    assert!(
        ec.contains(
            "wire:     32 bits a1+0x20, 1 bit a1+0x24
"
        ),
        "{ec}"
    );
    let has = function_summary(&p, &a, &o, 0x1660).unwrap();
    assert!(
        has.contains("declared: bool Cls::Has(int) const\n"),
        "{has}"
    );
    let gt = function_summary(&p, &a, &o, 0x18e0).unwrap();
    assert!(gt.contains("hints:    a1: Der *, result: Base *\n"), "{gt}");
    let vr = function_summary(&p, &a, &o, 0x1770).unwrap();
    let slot = name_of(&a, &o, 0x1200);
    assert!(vr.contains(&format!("virtual:  1 [{slot}]\n")), "{vr}");
    assert!(!has.contains("virtual:"), "{has}");
    assert!(
        has.contains("class:    Cls (class_layout(\"Cls\")"),
        "{has}"
    );
    assert!(!u.contains("declared:"), "{u}");
}

/// Function disassembly labels block starts, names call targets, and lists
/// exactly the function's six instructions.
#[test]
fn disasm_function_labels_and_names_targets() {
    use borer_engine::analysis::render::disasm_function;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = disasm_function(&p, &a, &o, 0x1000, 100, false).unwrap();
    assert!(text.contains("L_1005:"), "{text}");
    assert!(text.contains("; sub_1020"), "call target not named: {text}");
    assert!(
        text.lines().filter(|l| l.starts_with("0x")).count() == 6,
        "{text}"
    );
}

/// Functions take the names of the signature strings only they can be.
///
/// `NM2` is named from the string only it references; `NM`, whose only
/// signature string `NM2` also references, is named once `NM2` has its own
/// name; a symbol-named function is not marked inferred.
#[test]
fn functions_are_named_from_signature_strings() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let nm2 = a.function(0x15e0).expect("NM2 found");
    assert_eq!(nm2.name.as_deref(), Some("Foo::Baz"));
    assert!(nm2.name_inferred);
    let nm = a.function(0x15d0).expect("NM found");
    assert_eq!(nm.name.as_deref(), Some("Foo::Bar"));
    assert!(nm.name_inferred);
    let cs = a.function(0x13d0).expect("CS found");
    assert_eq!(cs.name.as_deref(), Some("exported_cs"));
    assert!(!cs.name_inferred);
    let am1 = a.function(0x1980).expect("AM1 found");
    assert_eq!(am1.name.as_deref(), Some("Acc::Get"));
    let am2 = a.function(0x1990).expect("AM2 found");
    assert!(am2.name.is_none(), "{:?}", am2.name);
}

/// Constructors give classes their vtables and parents.
///
/// `Der::Der` calls `Base::Base` with `this` and then stores `Der`'s vtable,
/// whose two slots are read up to the terminating zero word; the unnamed
/// function storing the same vtable becomes `Der::ctor_or_dtor`; the layout
/// shows parent, vtable and slots, and `Base` lists `Der` as derived.
#[test]
fn constructors_give_classes_vtables_and_parents() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let der = a.classes.by_name.get("Der").expect("Der");
    assert_eq!(der.vtable, Some(0x22a0));
    assert_eq!(der.slots, vec![0x1870, 0x1200]);
    assert_eq!(der.parent.as_deref(), Some("Base"));
    assert_eq!(der.ctors, vec![0x16f0, 0x1710, 0x1730]);
    let base = a.classes.by_name.get("Base").expect("Base");
    assert_eq!((base.vtable, base.parent.as_deref()), (Some(0x2280), None));
    assert_eq!(base.slots, vec![0x1200, 0x11e0]);
    assert_eq!(
        a.classes.vtables.get(&0x22a0).map(String::as_str),
        Some("Der")
    );
    let uc = a.function(0x1730).expect("UC");
    assert_eq!(uc.name.as_deref(), Some("Der::ctor_or_dtor"));
    assert!(uc.name_inferred);
    let o = Overlay::default();
    let layout = class_layout(&p, &a, &o, "Der").expect("layout");
    let text = render_layout(&layout, &a, &o);
    assert!(text.contains("parent:  Base\n"), "{text}");
    let slots = format!(
        "vftable: 0x22a0 (2 slots)\n  [0] {}\n  [1] {}\n",
        name_of(&a, &o, 0x1870),
        name_of(&a, &o, 0x1200)
    );
    assert!(text.contains(&slots), "{text}");
    assert!(text.contains("+0x0    vftable"), "{text}");
    let base_layout = class_layout(&p, &a, &o, "Base").expect("base layout");
    let base_text = render_layout(&base_layout, &a, &o);
    assert!(base_text.contains("derived: Der\n"), "{base_text}");
    assert!(text.contains("derived: Der2\n"), "{text}");
}

/// Virtual method names travel along the slot index.
///
/// `Der2::Foo` overrides slot 0 of `Der`'s table, so the unnamed function
/// there becomes `Der::Foo`; `Base`'s slot 0 is an export without a class
/// and keeps its name.
#[test]
fn virtual_method_names_follow_the_slot() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let dv = a.function(0x1870).expect("DV");
    assert_eq!(dv.name.as_deref(), Some("Der::Foo"));
    assert!(dv.name_inferred);
    let base_slot0 = a.function(0x1200).expect("P");
    assert!(base_slot0.name.as_deref().is_none_or(|n| !n.contains("::")));
}

/// A method passing its own `this` to an undeclared function types that
/// function's parameter.
///
/// `Der::Tick` calls `HT` with `this`, so `HT`'s first parameter is hinted
/// `Der` and `HT` counts as a method of `Der`; a slot of `Der`'s table (`DV`)
/// and one of `Base`'s (`Q`) are hinted their table's class; `HU2`, two
/// calls away from `Der::Tick2`, is hinted in the second round.
#[test]
fn callers_hint_the_parameter_class() {
    use borer_engine::analysis::classes::methods_of;
    let p = fixture();
    let a = Analysis::compute(&p);
    let ht = a.function(0x18d0).expect("HT");
    assert_eq!(ht.param_hints.get(&0).map(String::as_str), Some("Der"));
    assert!(methods_of(&a, &Overlay::default(), "Der").contains(&0x18d0));
    let dv = a.function(0x1870).expect("DV");
    assert_eq!(dv.param_hints.get(&0).map(String::as_str), Some("Der"));
    let q = a.function(0x11e0).expect("Q");
    assert_eq!(q.param_hints.get(&0).map(String::as_str), Some("Base"));
    let hu2 = a.function(0x1a40).expect("HU2");
    assert_eq!(hu2.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A call result or a field passed as another method's `this` is typed.
///
/// `Der::Poll` passes `GT`'s result and its field at 0x10 to `Base::Base`,
/// so `GT` returns a `Base *` and `Der`'s field at 0x10 is a `Base *`, which
/// the layout shows; `Der::Chk`'s guarded assert names the field at 8
/// `count`.
#[test]
fn call_results_and_fields_are_typed_by_their_use() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let gt = a.function(0x18e0).expect("GT");
    assert_eq!(gt.ret_hint.as_deref(), Some("Base"));
    assert_eq!(
        a.classes
            .field_hints
            .get(&("Der".to_owned(), 0x10))
            .map(String::as_str),
        Some("Base")
    );
    assert_eq!(
        a.classes
            .field_types
            .get(&("Der".to_owned(), 0x28))
            .map(String::as_str),
        Some("Core::Ptr<Der>")
    );
    let o = Overlay::default();
    let layout = class_layout(&p, &a, &o, "Der").expect("layout");
    let text = render_layout(&layout, &a, &o);
    assert!(text.contains("+0x10   Base *"), "{text}");
    assert!(text.contains("+0x28   Core::Ptr<Der>"), "{text}");
    assert!(text.contains("+0x8    u32 count"), "{text}");
}

/// A constructor storing `this` into the TLS block registers a singleton.
///
/// `Tls::Tls` stores at offset 0x10, so that slot is `Tls`, and the getter
/// `TG` returning that slot returns a `Tls *`; `Glob::Glob` stores `this`
/// in the global at 0x27c0, which holds a `Glob`; both layouts say where
/// their singleton lives.
#[test]
fn constructors_register_tls_singletons() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes.tls_slots.get(&0x10).map(String::as_str),
        Some("Tls")
    );
    let tg = a.function(0x1ab0).expect("TG");
    assert_eq!(tg.ret_hint.as_deref(), Some("Tls"));
    assert_eq!(
        a.classes.global_hints.get(&0x27c0).map(String::as_str),
        Some("Glob")
    );
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let o = Overlay::default();
    let tls = class_layout(&p, &a, &o, "Tls").expect("Tls layout");
    assert!(render_layout(&tls, &a, &o).contains("singleton: TLS slot 0x10\n"));
    let glob = class_layout(&p, &a, &o, "Glob").expect("Glob layout");
    assert!(render_layout(&glob, &a, &o).contains("singleton: global 0x27c0\n"));
}

/// The class layout lists a class's constructors and factories by name.
///
/// `Ns::Thing` has the constructor `DK`, named `Ns::Thing::ctor_or_dtor`;
/// `Ns::T3` has the factory `CI`, named `Ns::T3::create`.
#[test]
fn class_layout_lists_constructors_and_factories() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let thing = class_layout(&p, &a, &o, "Ns::Thing").expect("Ns::Thing layout");
    assert!(render_layout(&thing, &a, &o).contains(
        "constructors: Ns::Thing::ctor_or_dtor
"
    ));
    let t3 = class_layout(&p, &a, &o, "Ns::T3").expect("Ns::T3 layout");
    assert!(render_layout(&t3, &a, &o).contains(
        "factories: Ns::T3::create
"
    ));
}

/// A class layout is asked for by the name the classes listing prints,
/// bare or qualified, in any case.
///
/// `borer://classes` prints `Thing (Ns::Thing)` for a class registered by
/// its last segment, and an agent asks `class_layout` for `Thing`; the
/// answer was `no function belongs to class 'Thing'`. A bare name is the
/// class whose last segment it is, the first by name when several, and a
/// name is matched in any case, as `resolve` matches a function.
#[test]
fn class_layout_resolves_the_name_the_classes_listing_prints() {
    use borer_engine::analysis::classes::{class_layout, resolve_class};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        resolve_class(&a, &o, "Thing").as_deref(),
        Some("Ns::Thing"),
        "a bare name is the class whose last segment it is"
    );
    assert_eq!(
        resolve_class(&a, &o, "ns::thing").as_deref(),
        Some("Ns::Thing"),
        "a qualified name is matched in any case"
    );
    assert_eq!(resolve_class(&a, &o, "t3").as_deref(), Some("Ns::T3"));
    assert_eq!(resolve_class(&a, &o, "NoSuchClass"), None);
    assert_eq!(resolve_class(&a, &o, ""), None);
    let bare = class_layout(&p, &a, &o, "Thing").expect("Thing resolves to Ns::Thing");
    let full = class_layout(&p, &a, &o, "Ns::Thing").expect("Ns::Thing layout");
    assert_eq!(bare, full, "the bare name answers with the same layout");
    assert_eq!(
        bare.name, "Ns::Thing",
        "the layout is named as the methods qualify it"
    );
}

/// A call through the deleting destructor's slot with `1` alone reads as
/// `delete` whatever class the receiver is known to have.
///
/// Thirty-two classes `Ci`, each with a constructor `Ci::Ci` storing its
/// table (`lea rax, [table]; mov [rcx], rax; ret`) and a destructor
/// `Ci::~Ci` in slot 0, make slot 0 the program's deleting destructor.
/// `C0::Kill`, slot 1 of `C0`'s table, is `mov rax, [rcx]; mov edx, 1;
/// call [rax]; ret`: its `this` is a `C0`, so the slot resolves to
/// `C0::~C0`, and the call is still the `delete(this)` it reads as on an
/// object of unknown class, never `this->~C0(1)`.
#[test]
fn a_typed_deleting_destructor_call_reads_as_delete() {
    /// Classes holding a destructor in slot 0.
    const CLASSES: u64 = 32;
    let (text, table) = (0x1000_u64, 0x3000_u64);
    let mut bytes = vec![0xccu8; 0x3000];
    let mut symbols = Vec::new();
    let mut put = |va: u64, code: &[u8]| {
        let at = usize::try_from(va - text).expect("in .text");
        bytes[at..at + code.len()].copy_from_slice(code);
    };
    for i in 0..CLASSES {
        let ctor = text + i * 0x20;
        let vt = table + i * 0x18;
        let disp = i32::try_from(vt - (ctor + 7)).expect("near").to_le_bytes();
        put(
            ctor,
            &[
                0x48, 0x8d, 0x05, disp[0], disp[1], disp[2], disp[3], // ASM: lea rax, [table]
                0x48, 0x89, 0x01, // ASM: mov [rcx], rax
                0xc3, // ASM: ret
            ],
        );
        put(ctor + 0x10, &[0xc3]); // ASM: ret
        symbols.push((format!("C{i}::C{i}"), ctor));
        symbols.push((format!("C{i}::~C{i}"), ctor + 0x10));
    }
    put(0x1900, &[0xc3]); // ASM: ret
    put(
        0x1800,
        &[
            0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
            0xba, 0x01, 0x00, 0x00, 0x00, // ASM: mov edx, 1
            0xff, 0x10, // ASM: call [rax]
            0xc3, // ASM: ret
        ],
    );
    symbols.push(("C0::Kill".to_owned(), 0x1800));
    for i in 0..CLASSES {
        let at = usize::try_from(table - text + i * 0x18).expect("in .rdata");
        bytes[at..at + 8].copy_from_slice(&(text + i * 0x20 + 0x10).to_le_bytes());
        let second: u64 = if i == 0 { 0x1800 } else { 0x1900 };
        bytes[at + 8..at + 16].copy_from_slice(&second.to_le_bytes());
        bytes[at + 16..at + 24].copy_from_slice(&0_u64.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1800),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x2000, false, true),
            Section::mapped(".rdata", 0x3000, 0x2000, 0x1000, false, false),
        ],
    );
    p.symbols = symbols
        .into_iter()
        .map(|(name, addr)| Symbol {
            name,
            addr,
            kind: SymbolKind::Export,
        })
        .collect();
    let out = decompiled(&p, 0x1800);
    assert!(out.contains("C0 *this"), "{out}");
    assert!(out.contains("delete(this)"), "{out}");
}

/// A method tail-jumping to an undeclared function with its own `this` in
/// the argument register types that function's parameter, as a call does,
/// when the function reads it.
///
/// `Cls::Go` is `test rdx, rdx; jne T2; push rbx; mov rbx, rcx; mov rcx,
/// rbx; pop rbx; jmp T1`: both jumps hand `this` on unchanged, so `T1` and
/// `T2`, exported without a class and reached by nothing else, take `Cls`
/// for their first parameter. `Cls::Make` is `jmp T3`, and `T3` writes
/// `ecx` before it reads it: what `rcx` held is no argument of its.
#[test]
fn a_tail_jump_hints_the_callee_parameter_class() {
    let mut bytes = vec![0xccu8; 0x2000];
    let code = [
        0x48, 0x85, 0xd2, // ASM: test rdx, rdx
        0x75, 0x5b, // ASM: jne 0x1060
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0x5b, // ASM: pop rbx
        0xe9, 0x2e, 0x00, 0x00, 0x00, // ASM: jmp 0x1040
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x1040..0x1044].copy_from_slice(&[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ]);
    bytes[0x1060..0x1064].copy_from_slice(&[
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0xc3, // ASM: ret
    ]);
    bytes[0x10a0..0x10a5].copy_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]); // ASM: jmp 0x10c0
    bytes[0x10c0..0x10c8].copy_from_slice(&[
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
    ]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    p.symbols = [
        ("Cls::Go", 0x1000),
        ("t1", 0x1040),
        ("t2", 0x1060),
        ("Cls::Make", 0x10a0),
        ("t3", 0x10c0),
    ]
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Export,
    })
    .to_vec();
    let a = Analysis::compute(&p);
    for target in [0x1040, 0x1060] {
        let f = a.function(target).expect("the tail callee is a function");
        assert_eq!(
            f.param_hints.get(&0).map(String::as_str),
            Some("Cls"),
            "{target:#x}"
        );
    }
    let t3 = a
        .function(0x10c0)
        .expect("the third tail callee is a function");
    assert!(t3.param_hints.is_empty(), "{:?}", t3.param_hints);
}

/// Builds a raw x86-64 program from code pieces and exported names, with
/// tables of code pointers in a read-only section.
///
/// # Arguments
///
/// * `code` - `(address, bytes)` pieces of `.text` (0x1000..0x2000).
/// * `tables` - `(address, entries)` tables in `.rdata` (0x2000..0x3000).
/// * `names` - `(name, address)` exports.
fn raw_classes(code: &[(u64, &[u8])], tables: &[(u64, &[u64])], names: &[(&str, u64)]) -> Program {
    let mut bytes = vec![0xccu8; 0x2000];
    for (va, piece) in code {
        let at = borer_engine::num::saturating_usize(va - 0x1000);
        bytes[at..at + piece.len()].copy_from_slice(piece);
    }
    for (va, entries) in tables {
        let at = borer_engine::num::saturating_usize(va - 0x1000);
        for (k, e) in entries.iter().enumerate() {
            bytes[at + 8 * k..at + 8 * k + 8].copy_from_slice(&e.to_le_bytes());
        }
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = names
        .iter()
        .map(|(name, addr)| Symbol {
            name: (*name).to_owned(),
            addr: *addr,
            kind: SymbolKind::Export,
        })
        .collect();
    p
}

/// A function a class's table holds is a method of that class, whatever a
/// derived class's override hands it.
///
/// `Base::Base` stores `Base`'s table (`M`, `N`) and `Der::Der` calls it
/// before storing `Der`'s (`Der::Foo`, `N`). `Der::Foo` overrides `M` and
/// ends `jmp M`, handing on its `this`, a `Der`: `M` stays a method of
/// `Base`, the class whose table holds it, never `Der`.
#[test]
fn a_derived_override_does_not_narrow_its_base_method() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let m: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let foo: &[u8] = &[0xe9, 0xbb, 0xff, 0xff, 0xff]; // ASM: jmp 0x1100
    let n: &[u8] = &[0xc3]; // ASM: ret
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1100, m),
            (0x1140, foo),
            (0x1160, n),
        ],
        &[(0x2000, &[0x1100, 0x1160]), (0x2010, &[0x1140, 0x1160])],
        &[
            ("Base::Base", 0x1000),
            ("Der::Der", 0x1020),
            ("m", 0x1100),
            ("Der::Foo", 0x1140),
            ("n", 0x1160),
        ],
    );
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes
            .by_name
            .get("Der")
            .and_then(|c| c.parent.as_deref()),
        Some("Base")
    );
    let m = a.function(0x1100).expect("M");
    assert_eq!(m.param_hints.get(&0).map(String::as_str), Some("Base"));
}

/// A parameter no caller types takes the most derived of the classes the
/// callees it is handed to accept, which bound it from above.
///
/// `Der` derives from `Base` as in the test above. `H`, which nothing
/// calls, hands its first parameter to `Base::M` and to `Der::N` (`push rbx;
/// mov rbx, rcx; call M; mov rcx, rbx; call N; pop rbx; ret`): it is a
/// `Der`, not merely the `Base` both accept.
#[test]
fn a_parameter_handed_to_two_callees_is_the_most_derived_they_accept() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let m: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let n: &[u8] = &[
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0xc3, // ASM: ret
    ];
    let h: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xf7, 0xfe, 0xff, 0xff, // ASM: call 0x1100
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0x4f, 0xff, 0xff, 0xff, // ASM: call 0x1160
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1100, m),
            (0x1160, n),
            (0x1180, &[0xc3]),
            (0x1200, h),
        ],
        &[(0x2000, &[0x1100, 0x1180]), (0x2010, &[0x1160, 0x1180])],
        &[
            ("Base::Base", 0x1000),
            ("Der::Der", 0x1020),
            ("Base::M", 0x1100),
            ("Der::N", 0x1160),
            ("h", 0x1200),
        ],
    );
    let a = Analysis::compute(&p);
    let h = a.function(0x1200).expect("H");
    assert_eq!(h.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A thunk that hands its argument on to a function reading it reads it
/// too, so a tail jump into the thunk types the thunk's parameter.
///
/// `Cls::Go` is `jmp T1`, `T1` is `jmp T2` and `T2` reads `[rcx+8]`: the
/// `this` of `Cls::Go` reaches `T2` through `T1`, and both are `Cls`.
#[test]
fn a_thunk_handing_its_argument_on_reads_it() {
    let go: &[u8] = &[0xe9, 0x1b, 0x00, 0x00, 0x00]; // ASM: jmp 0x1020
    let t1: &[u8] = &[0xe9, 0x1b, 0x00, 0x00, 0x00]; // ASM: jmp 0x1040
    let t2: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[(0x1000, go), (0x1020, t1), (0x1040, t2)],
        &[],
        &[("Cls::Go", 0x1000), ("t1", 0x1020), ("t2", 0x1040)],
    );
    let a = Analysis::compute(&p);
    for e in [0x1020, 0x1040] {
        let f = a.function(e).expect("a thunk");
        assert_eq!(
            f.param_hints.get(&0).map(String::as_str),
            Some("Cls"),
            "{e:#x}"
        );
    }
}

/// A member's `this` is at least the class its name gives, whatever
/// ancestor its callers only know the object as.
///
/// `Der` derives from `Base` as above. `Base::Call` hands its own `this`, a
/// `Base`, to `Der::Run` (`call Run; ret`), which reads `[rcx+0x10]`: `Run`
/// is `Der`'s method, so its `this` is a `Der`.
#[test]
fn a_member_keeps_the_class_its_name_gives() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let call: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1180
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let run: &[u8] = &[
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1080, call),
            (0x1160, &[0xc3]),
            (0x1180, run),
        ],
        &[(0x2000, &[0x1160, 0x1160]), (0x2010, &[0x1160, 0x1160])],
        &[
            ("Base::Base", 0x1000),
            ("Der::Der", 0x1020),
            ("Base::Call", 0x1080),
            ("Der::Run", 0x1180),
        ],
    );
    let a = Analysis::compute(&p);
    let run = a.function(0x1180).expect("Run");
    assert_eq!(run.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A function a class's table holds keeps that class even when its name,
/// from the base table it stores, says otherwise.
///
/// `Der::Der` stores `Der`'s table and calls no base constructor, so no
/// parent links `Der` to `Base`. `D` stores `Base`'s table, the base phase
/// of a derived destructor, which names it after `Base`, and only `Der`'s
/// table holds it: its `this` is a `Der`.
#[test]
fn a_held_function_keeps_its_table_class_over_its_name() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xe9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let d: &[u8] = &[
        0x48, 0x8d, 0x05, 0x79, 0x0e, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1180, d),
            (0x1190, &[0xc3]),
        ],
        &[(0x2000, &[0x1190, 0x1190]), (0x2010, &[0x1180, 0x1190])],
        &[("Base::Base", 0x1000), ("Der::Der", 0x1020)],
    );
    let a = Analysis::compute(&p);
    let d = a.function(0x1180).expect("D");
    assert!(
        d.name.as_deref().is_some_and(|n| n.starts_with("Base::")),
        "{:?}",
        d.name
    );
    assert_eq!(d.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A handler takes its class prefix from a class its callers hand it, never
/// from an ancestor wider than all of them.
///
/// `A` and `B` derive from `Base`. `H` prints the type check of `Cmd::Xc`'s
/// handler and `A::Go` and `B::Go` call it with their `this`: it is a
/// `Base`, which neither caller said, so its name stays `HandleXc`. `H2`,
/// the handler of `Cmd::Yc`, is called by `A::Go2` alone and is
/// `A::HandleYc`.
#[test]
fn a_handler_takes_no_prefix_wider_than_its_callers() {
    /// Packs text, NUL-terminated, into little-endian words.
    fn words(text: &str) -> Vec<u64> {
        let mut bytes = text.as_bytes().to_vec();
        bytes.resize(bytes.len() / 8 * 8 + 8, 0);
        bytes
            .chunks_exact(8)
            .map(|c| u64::from_le_bytes(c.try_into().expect("eight bytes")))
            .collect()
    }
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let a_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let b_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xb7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xd0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2020]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let call = |rel: u8| -> Vec<u8> {
        vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, rel, 0x00, 0x00, 0x00, // ASM: call the handler
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ]
    };
    let handler: &[u8] = &[
        0x48, 0x8d, 0x15, 0xf9, 0x0e, 0x00, 0x00, // ASM: lea rdx, [the type check]
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let (a_go, b_go, a_go2) = (call(0xf7), call(0xd7), call(0xf7));
    let xc = words("Command handler for type 'Cmd::Xc' called with command of wrong type");
    let yc = words("Command handler for type 'Cmd::Yc' called with command of wrong type");
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, a_ctor),
            (0x1040, b_ctor),
            (0x1100, &a_go),
            (0x1120, &b_go),
            (0x1140, &a_go2),
            (0x1180, &[0xc3]),
            (0x1200, handler),
            (0x1240, handler),
        ],
        &[
            (0x2000, &[0x1180, 0x1180]),
            (0x2010, &[0x1180, 0x1180]),
            (0x2020, &[0x1180, 0x1180]),
            (0x2100, &xc),
            (0x2140, &yc),
        ],
        &[
            ("Base::Base", 0x1000),
            ("A::A", 0x1020),
            ("B::B", 0x1040),
            ("A::Go", 0x1100),
            ("B::Go", 0x1120),
            ("A::Go2", 0x1140),
        ],
    );
    let a = Analysis::compute(&p);
    let name = |e: u64| a.function(e).and_then(|f| f.name.clone());
    assert_eq!(name(0x1240).as_deref(), Some("A::HandleYc"));
    assert_eq!(name(0x1200).as_deref(), Some("HandleXc"));
}

/// A member that never reads its first register bounds nothing by the
/// class its name gives.
///
/// `H`, which nothing calls, keeps its first parameter in `rbx`, calls the
/// factory `Cmd::Create` with it still in `rcx`, then hands it to `Obj::Run`,
/// which reads `[rcx+8]`. `Create` reads no argument, so only `Run` bounds
/// the parameter: it is an `Obj`.
#[test]
fn a_callee_never_reading_its_first_argument_bounds_no_class() {
    let create: &[u8] = &[
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let run: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let h: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xf7, 0xfe, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0x0f, 0xff, 0xff, 0xff, // ASM: call 0x1020
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[(0x1000, create), (0x1020, run), (0x1100, h)],
        &[],
        &[("Cmd::Create", 0x1000), ("Obj::Run", 0x1020), ("h", 0x1100)],
    );
    let a = Analysis::compute(&p);
    let h = a.function(0x1100).expect("H");
    assert_eq!(h.param_hints.get(&0).map(String::as_str), Some("Obj"));
}

/// A parameter whose class still flips from round to round when the rounds
/// stop has no class, whichever one the last round gave.
///
/// `A` and `U` derive from `Base`. `A::Go` calls `D` with its `this`; `B`,
/// which nothing calls, hands its first parameter to `U::Use` and to `D`.
/// `B` is the deepest class its callees accept and votes for `D` with it:
/// `D` is an `A`, so `B` is untyped (`U` and `A` share no line), so `D` is
/// an `A`, so `B` is a `U`, so `D` is a `Base`, and around again for ever.
#[test]
fn a_parameter_whose_class_keeps_flipping_has_none() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let a_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let u_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xb7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xd0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2020]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let read: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let b: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1220
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0xaf, 0xff, 0xff, 0xff, // ASM: call 0x1200
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, a_ctor),
            (0x1040, u_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, read),
            (0x1220, read),
            (0x1240, b),
        ],
        &[
            (0x2000, &[0x1180, 0x1180]),
            (0x2010, &[0x1180, 0x1180]),
            (0x2020, &[0x1180, 0x1180]),
        ],
        &[
            ("Base::Base", 0x1000),
            ("A::A", 0x1020),
            ("U::U", 0x1040),
            ("A::Go", 0x1100),
            ("d", 0x1200),
            ("U::Use", 0x1220),
            ("b", 0x1240),
        ],
    );
    let a = Analysis::compute(&p);
    for e in [0x1200, 0x1240] {
        let f = a.function(e).expect("a flipping function");
        assert_eq!(f.param_hints.get(&0), None, "{e:#x}");
    }
}

/// A function that never reads a register takes no class from what its
/// callers leave there; the tables holding it still type its `this`.
///
/// `Base::Go` calls `F`, a factory (`xor eax, eax; ret`), with its `this`
/// still in `rcx`: `F` has no `this` to type. `H`, a `ret` that `Base`'s
/// table holds, stays a `Base` method though it reads nothing either.
#[test]
fn a_register_its_function_never_reads_takes_no_class_from_callers() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let factory: &[u8] = &[
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, factory),
        ],
        &[(0x2000, &[0x1180, 0x1180])],
        &[("Base::Base", 0x1000), ("Base::Go", 0x1100), ("f", 0x1200)],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1200).expect("F");
    assert_eq!(f.param_hints.get(&0), None);
    let h = a.function(0x1180).expect("H");
    assert_eq!(h.param_hints.get(&0).map(String::as_str), Some("Base"));
}

/// A callee's own use of a parameter outranks the class a single caller
/// hands on from its own hint.
///
/// `Wrong::Go` calls `C` with its `this` in `rdx`, so `C`'s second
/// parameter is a `Wrong`. `C` hands it on untouched to `F`, which moves it
/// to `rcx` and calls `Obj::Use`, which reads `[rcx+8]`: `F` uses it as an
/// `Obj`, which outranks what `C` was only told.
#[test]
fn a_callee_s_own_use_outranks_one_caller_s_hint() {
    let go: &[u8] = &[
        0x48, 0x89, 0xca, // ASM: mov rdx, rcx
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let c: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x89, 0xd1, // ASM: mov rcx, rdx
        0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1300
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let used: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[(0x1000, go), (0x1100, c), (0x1200, f), (0x1300, used)],
        &[],
        &[
            ("Wrong::Go", 0x1000),
            ("c", 0x1100),
            ("f", 0x1200),
            ("Obj::Use", 0x1300),
        ],
    );
    let a = Analysis::compute(&p);
    let c = a.function(0x1100).expect("C");
    assert_eq!(c.param_hints.get(&1).map(String::as_str), Some("Wrong"));
    let f = a.function(0x1200).expect("F");
    assert_eq!(f.param_hints.get(&1).map(String::as_str), Some("Obj"));
}

/// A callee using a parameter as the pointer a key-value pair starts with
/// leaves it the pair its single caller hands on.
///
/// As above, but the caller's class is `Util::KeyValuePair<Core::Ptr<Obj>,int>`
/// and `F` hands the parameter to `Core::Ptr<Obj>::Get`: the pair and its
/// key are one object seen at two depths, so the pair stands.
#[test]
fn a_use_of_a_pair_s_key_leaves_the_pair() {
    let go: &[u8] = &[
        0x48, 0x89, 0xca, // ASM: mov rdx, rcx
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let c: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x89, 0xd1, // ASM: mov rcx, rdx
        0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1300
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let get: &[u8] = &[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0xc3, // ASM: ret
    ];
    let pair = "Util::KeyValuePair<Core::Ptr<Obj>,int>";
    let go_name = format!("{pair}::Go");
    let p = raw_classes(
        &[(0x1000, go), (0x1100, c), (0x1200, f), (0x1300, get)],
        &[],
        &[
            (go_name.as_str(), 0x1000),
            ("c", 0x1100),
            ("f", 0x1200),
            ("Core::Ptr<Obj>::Get", 0x1300),
        ],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1200).expect("F");
    assert_eq!(f.param_hints.get(&1).map(String::as_str), Some(pair));
}

/// A function reads an argument register only on a path from its entry
/// that has not set it.
///
/// `Base::Go` calls `F` and `G` with its `this` in `rcx`. `F` sets `ecx`
/// and jumps back to code laid out before its entry that reads `[rcx+8]`:
/// it never reads the `this` it was handed, so it is no `Base`. `G` loads
/// `rcx` from `[rcx+8]`, reading it as it writes it: it is a `Base`.
#[test]
fn a_register_set_before_its_read_on_the_path_is_no_argument() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0x37, 0x01, 0x00, 0x00, // ASM: call 0x1240
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0x6f, 0x01, 0x00, 0x00, // ASM: call 0x1280
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let shared: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0xb9, 0x10, 0x00, 0x00, 0x00, // ASM: mov ecx, 0x10
        0xe9, 0xb6, 0xff, 0xff, 0xff, // ASM: jmp 0x1200
    ];
    let g: &[u8] = &[
        0x48, 0x8b, 0x49, 0x08, // ASM: mov rcx, [rcx+8]
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, shared),
            (0x1240, f),
            (0x1280, g),
        ],
        &[(0x2000, &[0x1180, 0x1180])],
        &[
            ("Base::Base", 0x1000),
            ("Base::Go", 0x1100),
            ("f", 0x1240),
            ("g", 0x1280),
        ],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1240).expect("F");
    assert_eq!(f.param_hints.get(&0), None);
    let g = a.function(0x1280).expect("G");
    assert_eq!(g.param_hints.get(&0).map(String::as_str), Some("Base"));
}

/// Code laid out before a function's entry hands its callees nothing: the
/// function reaches it with registers it set itself.
///
/// `Base::Go` calls `F` with its `this` in `rcx`. `F` sets `ecx` and jumps
/// back to code laid out before its entry that calls `Obj::Use`, which
/// reads `[rcx+8]`: `F` hands on no `this`, so it is no `Base`.
#[test]
fn code_before_the_entry_hands_its_callees_nothing() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0x37, 0x01, 0x00, 0x00, // ASM: call 0x1240
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let shared: &[u8] = &[
        0xe8, 0xfb, 0x00, 0x00, 0x00, // ASM: call 0x1300
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0xb9, 0x10, 0x00, 0x00, 0x00, // ASM: mov ecx, 0x10
        0xe9, 0xb6, 0xff, 0xff, 0xff, // ASM: jmp 0x1200
    ];
    let used: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, shared),
            (0x1240, f),
            (0x1300, used),
        ],
        &[(0x2000, &[0x1180, 0x1180])],
        &[
            ("Base::Base", 0x1000),
            ("Base::Go", 0x1100),
            ("f", 0x1240),
            ("Obj::Use", 0x1300),
        ],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1240).expect("F");
    assert_eq!(f.param_hints.get(&0), None);
}

/// A 32-bit method hands its `this` on in `ecx`, by a call or a tail jump,
/// to a callee that reads it; one that never reads `ecx`, or only pushes
/// it to make room on the stack, takes nothing.
///
/// `Base::Go` (`push esi; mov esi, ecx; call F; mov ecx, esi; call G; pop
/// esi; ret`) calls `F`, which reads `[ecx+4]`, and `G`, which reads only
/// `[esp+4]`. `Base::Jmp` jumps to `T`, which reads `[ecx+8]`.
/// `Base::Go2` calls `P`, which pushes `ecx` as MSVC reserves a word of
/// frame and reads it no other way. `F` and `T` are `Base`; `G` and `P`
/// have no class.
#[test]
fn a_32_bit_this_reaches_the_callees_reading_ecx() {
    let ctor: &[u8] = &[
        0xc7, 0x01, 0x00, 0x20, 0x00, 0x00, // ASM: mov dword [ecx], 0x2000
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x56, // ASM: push esi
        0x8b, 0xf1, // ASM: mov esi, ecx
        0xe8, 0xf8, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x8b, 0xce, // ASM: mov ecx, esi
        0xe8, 0x11, 0x01, 0x00, 0x00, // ASM: call 0x1220
        0x5e, // ASM: pop esi
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0x8b, 0x41, 0x04, // ASM: mov eax, [ecx+4]
        0xc3, // ASM: ret
    ];
    let g: &[u8] = &[
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
        0xc3, // ASM: ret
    ];
    let jmp: &[u8] = &[0xe9, 0x1b, 0x00, 0x00, 0x00]; // ASM: jmp 0x1260
    let t: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [ecx+8]
        0xc3, // ASM: ret
    ];
    let go2: &[u8] = &[
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x12a0
        0xc3, // ASM: ret
    ];
    let room: &[u8] = &[
        0x51, // ASM: push ecx
        0xc7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [esp], 0
        0x58, // ASM: pop eax
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0xccu8; 0x2000];
    for (va, piece) in [
        (0x1000, ctor),
        (0x1100, go),
        (0x1180, &[0xc3][..]),
        (0x1200, f),
        (0x1220, g),
        (0x1240, jmp),
        (0x1260, t),
        (0x1280, go2),
        (0x12a0, room),
    ] {
        let at = borer_engine::num::saturating_usize(va - 0x1000);
        bytes[at..at + piece.len()].copy_from_slice(piece);
    }
    for (k, slot) in [0x1180u32, 0x1180].into_iter().enumerate() {
        bytes[0x1000 + 4 * k..0x1000 + 4 * k + 4].copy_from_slice(&slot.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = [
        ("Base::Base", 0x1000),
        ("Base::Go", 0x1100),
        ("f", 0x1200),
        ("g", 0x1220),
        ("Base::Jmp", 0x1240),
        ("t", 0x1260),
        ("Base::Go2", 0x1280),
        ("p", 0x12a0),
    ]
    .into_iter()
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Export,
    })
    .collect();
    let a = Analysis::compute(&p);
    let class = |e: u64| a.function(e).and_then(|f| f.param_hints.get(&0).cloned());
    assert_eq!(class(0x1200).as_deref(), Some("Base"));
    assert_eq!(class(0x1260).as_deref(), Some("Base"));
    assert_eq!(class(0x1220), None);
    assert_eq!(class(0x12a0), None);
}

/// A 32-bit method its name gives no class prints the class its `this`
/// was typed as.
///
/// `Base::Base` stores `Base`'s table; `Base::Go` calls `F` with its `this`
/// in `ecx`, and `F` reads `[ecx+4]`: `F` prints as taking a `Base *this`.
#[test]
fn a_32_bit_method_prints_the_class_of_its_this() {
    let ctor: &[u8] = &[
        0xc7, 0x01, 0x00, 0x20, 0x00, 0x00, // ASM: mov dword [ecx], 0x2000
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0xe8, 0xfb, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0x8b, 0x41, 0x04, // ASM: mov eax, [ecx+4]
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0xccu8; 0x2000];
    for (va, piece) in [
        (0x1000, ctor),
        (0x1100, go),
        (0x1180, &[0xc3][..]),
        (0x1200, f),
    ] {
        let at = borer_engine::num::saturating_usize(va - 0x1000);
        bytes[at..at + piece.len()].copy_from_slice(piece);
    }
    for (k, slot) in [0x1180u32, 0x1180].into_iter().enumerate() {
        bytes[0x1000 + 4 * k..0x1000 + 4 * k + 4].copy_from_slice(&slot.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = [("Base::Base", 0x1000), ("Base::Go", 0x1100), ("f", 0x1200)]
        .into_iter()
        .map(|(name, addr)| Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Export,
        })
        .collect();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text =
        borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1200).expect("decompiles");
    assert!(text.contains("(Base *this)"), "{text}");
}

/// Of an object and the member it starts with, a parameter is the object
/// whenever a vote or a use names it, and the member only when nothing else
/// does.
///
/// `Util::Dict::Add` hands its `this` to `Util::List::Push`: a `Util::Dict`
/// starts with a `Util::List`. `H` is called by `Util::Dict::Find` and by
/// `Util::List::Scan`, `G` hands its parameter to `Util::List::Push` and to
/// `Util::Dict::Size`: both are a `Util::Dict`. `K`, called by
/// `Util::List::Scan` alone, is a `Util::List`. `Util::Map<Key>::Add` hands
/// its `this` to `Util::Vec<Util::Pair<Key> >::Push`, so every
/// `Util::Map<T>` starts with a `Util::Vec<Util::Pair<T> >`: `N`, handed to
/// `Util::Vec<Util::Pair<Other> >::Push` and to `Util::Map<Other>::Size`,
/// is a `Util::Map<Other>`. `Holder::Setup` hands its field at `+0x10` to
/// `Util::List::Push`, to `Util::Dict::Size` and to `Q`: the field is a
/// `Util::Dict`, and so is `Q`.
#[test]
fn a_container_outranks_the_member_it_starts_with() {
    let call = |rel: [u8; 4]| -> Vec<u8> {
        vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, rel[0], rel[1], rel[2], rel[3], // ASM: call the member
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ]
    };
    let both = |first: [u8; 4], second: [u8; 4]| -> Vec<u8> {
        vec![
            0x53, // ASM: push rbx
            0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
            0xe8, first[0], first[1], first[2], first[3], // ASM: call the first
            0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
            0xe8, second[0], second[1], second[2], second[3], // ASM: call the second
            0x5b,      // ASM: pop rbx
            0xc3,      // ASM: ret
        ]
    };
    let read: &[u8] = &[
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ];
    let read8: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let add = call([0xf7, 0x00, 0x00, 0x00]); // ASM: call 0x1100
    let find = call([0xf7, 0x00, 0x00, 0x00]); // ASM: call 0x1300
    let scan = both([0xb7, 0x00, 0x00, 0x00], [0x2f, 0x01, 0x00, 0x00]); // ASM: call 0x1300; call 0x1380
    let g = both([0xb7, 0xfd, 0xff, 0xff], [0xcf, 0xfd, 0xff, 0xff]); // ASM: call 0x1100; call 0x1120
    let map_add = call([0x37, 0x00, 0x00, 0x00]); // ASM: call 0x1440
    let n = both([0x37, 0x00, 0x00, 0x00], [0x4f, 0x00, 0x00, 0x00]); // ASM: call 0x14c0; call 0x14e0
    let setup: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0x48, 0x8d, 0x4b, 0x10, // ASM: lea rcx, [rbx+0x10]
        0xe8, 0xf3, 0xfb, 0xff, 0xff, // ASM: call 0x1100
        0x48, 0x8d, 0x4b, 0x10, // ASM: lea rcx, [rbx+0x10]
        0xe8, 0x0a, 0xfc, 0xff, 0xff, // ASM: call 0x1120
        0x48, 0x8d, 0x4b, 0x10, // ASM: lea rcx, [rbx+0x10]
        0xe8, 0x61, 0x00, 0x00, 0x00, // ASM: call 0x1580
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, &add),
            (0x1100, read),
            (0x1120, read8),
            (0x1200, &find),
            (0x1240, &scan),
            (0x1300, read),
            (0x1340, &g),
            (0x1380, read),
            (0x1400, &map_add),
            (0x1440, read),
            (0x1480, &n),
            (0x14c0, read),
            (0x14e0, read8),
            (0x1500, setup),
            (0x1580, read),
        ],
        &[],
        &[
            ("Util::Dict::Add", 0x1000),
            ("Util::List::Push", 0x1100),
            ("Util::Dict::Size", 0x1120),
            ("Util::Dict::Find", 0x1200),
            ("Util::List::Scan", 0x1240),
            ("h", 0x1300),
            ("g", 0x1340),
            ("k", 0x1380),
            ("Util::Map<Key>::Add", 0x1400),
            ("Util::Vec<Util::Pair<Key> >::Push", 0x1440),
            ("n", 0x1480),
            ("Util::Vec<Util::Pair<Other> >::Push", 0x14c0),
            ("Util::Map<Other>::Size", 0x14e0),
            ("Holder::Setup", 0x1500),
            ("q", 0x1580),
        ],
    );
    let a = Analysis::compute(&p);
    let class = |e: u64| a.function(e).and_then(|f| f.param_hints.get(&0).cloned());
    assert_eq!(class(0x1300).as_deref(), Some("Util::Dict"));
    assert_eq!(class(0x1340).as_deref(), Some("Util::Dict"));
    assert_eq!(class(0x1380).as_deref(), Some("Util::List"));
    assert_eq!(class(0x1480).as_deref(), Some("Util::Map<Other>"));
    assert_eq!(class(0x1580).as_deref(), Some("Util::Dict"));
}

/// Evidence a later round finds revises a parameter's class: two unrelated
/// classes leave it untyped, whichever arrived first.
///
/// `A::F` calls `U` with its `this` in the first round; `B::G` calls `H`,
/// which is typed `B` in that round and calls `U` with the same `this` in
/// the next. `A` and `B` have no common ancestor, so `U` is neither.
#[test]
fn a_later_conflicting_vote_revises_the_first_class() {
    let call = |target: u64, from: u64| -> Vec<u8> {
        let rel = i32::try_from(target).expect("near") - i32::try_from(from + 9).expect("near");
        let r = rel.to_le_bytes();
        vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, r[0], r[1], r[2], r[3], // ASM: call target
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ]
    };
    let u: &[u8] = &[
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ];
    let (af, h, bg) = (
        call(0x1100, 0x1000),
        call(0x1100, 0x1040),
        call(0x1040, 0x1080),
    );
    let p = raw_classes(
        &[(0x1000, &af), (0x1040, &h), (0x1080, &bg), (0x1100, u)],
        &[],
        &[
            ("A::F", 0x1000),
            ("h", 0x1040),
            ("B::G", 0x1080),
            ("u", 0x1100),
        ],
    );
    let a = Analysis::compute(&p);
    let hint = |e: u64| {
        a.function(e)
            .expect("a function")
            .param_hints
            .get(&0)
            .cloned()
    };
    assert_eq!(hint(0x1040).as_deref(), Some("B"));
    assert_eq!(hint(0x1100), None, "A and B share no ancestor");
}

/// A class one caller only hands on settles on a callee no other caller
/// contradicts, and on no callee another caller hands data of no class or
/// of an unrelated one.
///
/// `N::A::BindM` (a signature string names it) hands its declared
/// `const N::M &` to the third argument of `sink`, `sink2` and `sink3`.
/// `N::A::BindF` copies the `N::F` its own third argument points at into a
/// local and hands `sink` that copy, as a blob binder hands
/// `sqlite3_bind_blob` the bytes of a `float4`; `k` hands `sink3` constant
/// bytes; `g` hands `sink2` a local nothing says the class of. `sink` and
/// `sink3` take no class, `sink2` stays an `N::M`.
#[test]
fn a_class_handed_on_once_yields_to_a_contradicting_caller() {
    let words = |text: &[u8]| -> Vec<u64> {
        text.chunks(8)
            .map(|c| {
                let mut w = [0u8; 8];
                w[..c.len()].copy_from_slice(c);
                u64::from_le_bytes(w)
            })
            .collect()
    };
    let root: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0xe8, 0xf2, 0x01, 0x00, 0x00, // ASM: call 0x1200
        0xe8, 0xed, 0x02, 0x00, 0x00, // ASM: call 0x1300
        0xe8, 0xe8, 0x03, 0x00, 0x00, // ASM: call 0x1400
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let bind_m: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
        0x48, 0x8d, 0x05, 0xf4, 0x0e, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x4c, 0x89, 0xc3, // ASM: mov rbx, r8
        0xe8, 0xec, 0x03, 0x00, 0x00, // ASM: call 0x1500
        0x49, 0x89, 0xd8, // ASM: mov r8, rbx
        0xe8, 0x04, 0x04, 0x00, 0x00, // ASM: call 0x1520
        0x49, 0x89, 0xd8, // ASM: mov r8, rbx
        0xe8, 0x1c, 0x04, 0x00, 0x00, // ASM: call 0x1540
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let bind_f: &[u8] = &[
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp, 0x48
        0x48, 0x8d, 0x05, 0x75, 0x0e, 0x00, 0x00, // ASM: lea rax, [0x2080]
        0x41, 0x0f, 0x10, 0x00, // ASM: movups xmm0, [r8]
        0x0f, 0x11, 0x44, 0x24, 0x30, // ASM: movups [rsp+0x30], xmm0
        0x4c, 0x8d, 0x44, 0x24, 0x30, // ASM: lea r8, [rsp+0x30]
        0xe8, 0xe2, 0x02, 0x00, 0x00, // ASM: call 0x1500
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp, 0x48
        0xc3, // ASM: ret
    ];
    let g: &[u8] = &[
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp, 0x48
        0x4c, 0x8d, 0x44, 0x24, 0x30, // ASM: lea r8, [rsp+0x30]
        0xe8, 0x12, 0x02, 0x00, 0x00, // ASM: call 0x1520
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp, 0x48
        0xc3, // ASM: ret
    ];
    let k: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x4c, 0x8d, 0x05, 0xf5, 0x0c, 0x00, 0x00, // ASM: lea r8, [0x2100]
        0xe8, 0x30, 0x01, 0x00, 0x00, // ASM: call 0x1540
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let sink: &[u8] = &[
        0x41, 0x8b, 0x00, // ASM: mov eax, [r8]
        0xc3, // ASM: ret
    ];
    let sig_m = words(b"void __cdecl N::A::BindM(int,const class N::M &)\0");
    let sig_f = words(b"void __cdecl N::A::BindF(int,const class N::F &)\0");
    let bytes = [0x8899_aabb_ccdd_eeff_u64, 0x0011_2233_4455_6677];
    let p = raw_classes(
        &[
            (0x1000, root),
            (0x1100, bind_m),
            (0x1200, bind_f),
            (0x1300, g),
            (0x1400, k),
            (0x1500, sink),
            (0x1520, sink),
            (0x1540, sink),
        ],
        &[(0x2000, &sig_m), (0x2080, &sig_f), (0x2100, &bytes)],
        &[
            ("root", 0x1000),
            ("g", 0x1300),
            ("k", 0x1400),
            ("sink", 0x1500),
            ("sink2", 0x1520),
            ("sink3", 0x1540),
        ],
    );
    let a = Analysis::compute(&p);
    let name = |e: u64| a.function(e).and_then(|f| f.name.clone());
    assert_eq!(name(0x1100).as_deref(), Some("N::A::BindM"));
    assert_eq!(name(0x1200).as_deref(), Some("N::A::BindF"));
    let hint = |e: u64| {
        a.function(e)
            .expect("a function")
            .param_hints
            .get(&2)
            .cloned()
    };
    assert_eq!(hint(0x1500), None, "a copied N::F reaches it");
    assert_eq!(hint(0x1520).as_deref(), Some("N::M"), "nothing contradicts");
    assert_eq!(hint(0x1540), None, "constant bytes reach it");
}

/// A parameter some call site hands a string literal holds no object, so
/// no other call site's class types it.
///
/// `Cls::G` passes its own `this` as `R`'s second argument (`mov rdx, rcx;
/// call R; ret`); `g` passes the file name `"util/a.cc"` there (`lea rdx,
/// [str]; call R; ret`), as every caller of an assertion reporter does.
/// `R`'s second parameter takes no class. `Cls::G2` passes its `this` to
/// `R2` the same way, and `g2` (`test ecx, ecx; jne L; lea rdx, [str]; ret;
/// L: call R2; ret`) loads the string only on the path that returns: the
/// call hands on its own `rdx`, so `R2` keeps `Cls`.
#[test]
fn a_string_literal_argument_vetoes_a_class() {
    let r: &[u8] = &[
        0x8b, 0x02, // ASM: mov eax, [rdx]
        0xc3, // ASM: ret
    ];
    let g_cls: &[u8] = &[
        0x48, 0x8b, 0xd1, // ASM: mov rdx, rcx
        0xe8, 0xd8, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0xc3, // ASM: ret
    ];
    let g: &[u8] = &[
        0x48, 0x8d, 0x15, 0xb9, 0x0f, 0x00, 0x00, // ASM: lea rdx, [0x2000]
        0xe8, 0xb4, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0xc3, // ASM: ret
    ];
    let g2_cls: &[u8] = &[
        0x48, 0x8b, 0xd1, // ASM: mov rdx, rcx
        0xe8, 0x98, 0x00, 0x00, 0x00, // ASM: call 0x1120
        0xc3, // ASM: ret
    ];
    let g2: &[u8] = &[
        0x85, 0xc9, // ASM: test ecx, ecx
        0x75, 0x08, // ASM: jne 0x106c
        0x48, 0x8d, 0x15, 0x95, 0x0f, 0x00, 0x00, // ASM: lea rdx, [0x2000]
        0xc3, // ASM: ret
        0xe8, 0xaf, 0x00, 0x00, 0x00, // ASM: call 0x1120
        0xc3, // ASM: ret
    ];
    let name = u64::from_le_bytes(*b"util/a.c");
    let tail = u64::from_le_bytes(*b"c\0\0\0\0\0\0\0");
    let p = raw_classes(
        &[
            (0x1020, g_cls),
            (0x1040, g),
            (0x1060, g2),
            (0x1080, g2_cls),
            (0x1100, r),
            (0x1120, r),
        ],
        &[(0x2000, &[name, tail])],
        &[
            ("Cls::G", 0x1020),
            ("g", 0x1040),
            ("g2", 0x1060),
            ("Cls::G2", 0x1080),
            ("r", 0x1100),
            ("r2", 0x1120),
        ],
    );
    let a = Analysis::compute(&p);
    let hint = |e: u64| {
        a.function(e)
            .expect("a function")
            .param_hints
            .get(&1)
            .cloned()
    };
    assert_eq!(hint(0x1100), None, "a literal reaches it");
    assert_eq!(
        hint(0x1120).as_deref(),
        Some("Cls"),
        "no literal reaches it"
    );
}

/// A variadic function's variable arguments are not typed slots: what one
/// caller hands there types nothing, and hands nothing back to a caller
/// passing a register on.
///
/// `L` homes `rdx`, `r8` and `r9` and takes `rdx`'s home for `va_start`
/// (`mov [rsp+0x10], rdx; mov [rsp+0x18], r8; mov [rsp+0x20], r9; sub rsp,
/// 0x28; lea r8, [rsp+0x38]; call X; add rsp, 0x28; ret`): one fixed
/// argument, then the list. `Cls::Go` calls it with `this` in `rcx` and in
/// `r8` (`mov r8, rcx; call L; ret`); `T` is `xor ecx, ecx; jmp L`, leaving
/// `r8` as its caller set it. `L`'s fixed argument is a `Cls`, its third
/// slot nothing, and `T` takes no class from it.
#[test]
fn a_variadic_callee_types_only_its_fixed_arguments() {
    let mut bytes = vec![0xccu8; 0x2000];
    let mut put = |va: usize, code: &[u8]| bytes[va..va + code.len()].copy_from_slice(code);
    put(
        0x1000,
        &[
            0x4c, 0x8b, 0xc1, // ASM: mov r8, rcx
            0xe8, 0xf8, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0xc3, // ASM: ret
        ],
    );
    put(
        0x1040,
        &[
            0x31, 0xc9, // ASM: xor ecx, ecx
            0xe9, 0xb9, 0x00, 0x00, 0x00, // ASM: jmp 0x1100
        ],
    );
    put(
        0x1100,
        &[
            0x48, 0x89, 0x54, 0x24, 0x10, // ASM: mov [rsp+0x10], rdx
            0x4c, 0x89, 0x44, 0x24, 0x18, // ASM: mov [rsp+0x18], r8
            0x4c, 0x89, 0x4c, 0x24, 0x20, // ASM: mov [rsp+0x20], r9
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0x4c, 0x8d, 0x44, 0x24, 0x38, // ASM: lea r8, [rsp+0x38]
            0xe8, 0xe3, 0x00, 0x00, 0x00, // ASM: call 0x1200
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ],
    );
    put(0x1200, &[0xc3]); // ASM: ret
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    p.symbols = [
        ("Cls::Go", 0x1000),
        ("t", 0x1040),
        ("l", 0x1100),
        ("x", 0x1200),
    ]
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Export,
    })
    .to_vec();
    let a = Analysis::compute(&p);
    let hints = |e: u64| a.function(e).expect("a function").param_hints.clone();
    assert_eq!(
        hints(0x1100),
        BTreeMap::from([(0, "Cls".to_owned())]),
        "the fixed argument only"
    );
    assert!(hints(0x1040).is_empty(), "{:?}", hints(0x1040));
}

/// A field's address passed to an undeclared function types that
/// function's parameter with the field's embedded type.
///
/// `Der::Pass` passes the address of its `Core::Ptr<Der>` field at 0x28 to
/// `UP`, so `UP`'s first parameter points at a `Core::Ptr<Der>`.
#[test]
fn field_addresses_type_the_callee_parameter() {
    let a = Analysis::compute(&fixture());
    assert_eq!(
        a.function(0x1118).and_then(|f| f.name.as_deref()),
        Some("Der::Pass")
    );
    let up = a.function(0x12f0).expect("UP");
    assert_eq!(
        up.param_hints.get(&0).map(String::as_str),
        Some("Core::Ptr<Der>")
    );
}

/// A function that never writes `rax` on its way to a `ret` hands it back
/// untouched.
///
/// `CK` compares `rcx` with a global and returns, jumping elsewhere on a
/// mismatch, so it preserves `rax`; `BL` writes `eax`, so it does not.
#[test]
fn functions_that_never_write_rax_preserve_it() {
    let a = Analysis::compute(&fixture());
    assert!(a.function(0x4041).is_some_and(|f| f.preserves_rax));
    assert!(a.function(0x1f30).is_some_and(|f| !f.preserves_rax));
}

/// Two copies of one function share a body fingerprint; a copy that
/// differs in an instruction does not.
///
/// `CL_A` and `CL_B` run the same code over different globals, so the
/// addresses they name are left out of the fingerprint and they form a
/// clone class; `CL_C` ends in a different instruction and stands alone.
#[test]
fn copies_of_one_function_share_a_fingerprint() {
    let a = Analysis::compute(&fixture());
    let hash = |e: u64| a.function(e).map(|f| f.body_hash);
    assert_eq!(hash(0x4220), hash(0x4240));
    assert_ne!(hash(0x4220), hash(0x4260));
    assert_eq!(a.clones_of(0x4220), [0x4220, 0x4240]);
    assert_eq!(a.clones_of(0x4240), [0x4220, 0x4240]);
    assert!(a.clones_of(0x4260).is_empty());
}

/// Thunks through different slots are no clones; thunks through one are.
///
/// The entry calls three functions of one `jmp [rip+slot]` each, the first
/// and the last through one slot and the middle through another: every
/// such thunk had one fingerprint, so a binary's thunks to different
/// imports were reported as running the same code.
#[test]
fn thunks_through_different_slots_are_no_clones() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xe8, 0x26, 0x00, 0x00, 0x00, // ASM: call 0x401030
        0xe8, 0x31, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xff, 0x25, 0xda, 0x0f, 0x00, 0x00]); // ASM: jmp [rip+0xfda]
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xff, 0x25, 0xd2, 0x0f, 0x00, 0x00]); // ASM: jmp [rip+0xfd2]
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xff, 0x25, 0xba, 0x0f, 0x00, 0x00]); // ASM: jmp [rip+0xfba]
    let mut bytes = vec![0u8; 0x2000];
    bytes[..code.len()].copy_from_slice(&code);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![
            Section::mapped(".text", 0x401_000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x402_000, 0x1000, 0x1000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    assert_eq!(a.clones_of(0x401_020), [0x401_020, 0x401_040]);
    assert!(a.clones_of(0x401_030).is_empty());
}

/// The function summary lists the other functions running the same code.
///
/// `CL_A` and `CL_B` are clones, so each summary names the other.
#[test]
fn function_summary_lists_clones() {
    use borer_engine::analysis::render::function_summary;
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let s = function_summary(&p, &a, &o, 0x4220).expect("summary");
    assert!(
        s.contains("clones:   1 other function runs this code"),
        "{s}"
    );
    assert!(s.contains("sub_4240"), "{s}");
    let alone = function_summary(&p, &a, &o, 0x4260).expect("summary");
    assert!(!alone.contains("clones:"), "{alone}");
}

/// A list of entries keeps one function per clone class and names the rest.
///
/// `CL_A` and `CL_B` are clones, so `CL_B` folds under `CL_A`; `CL_C`
/// stands alone.
#[test]
fn dedupe_keeps_one_function_per_clone_class() {
    let a = Analysis::compute(&fixture());
    let kept = a.dedupe_clones(&[0x4220, 0x4260, 0x4240]);
    assert_eq!(kept, vec![(0x4220, vec![0x4240]), (0x4260, vec![])]);
}

/// The references a function makes come back from the per-function index
/// in address order.
///
/// `CL_A` reads a global and calls `Q`.
#[test]
fn references_from_a_function_are_indexed() {
    let a = Analysis::compute(&fixture());
    let refs = a.refs_from(0x4220);
    let kinds: Vec<(u64, RefKind)> = refs.iter().map(|(t, s)| (*t, s.kind)).collect();
    assert!(kinds.contains(&(0x3090, RefKind::Data)), "{kinds:?}");
    assert!(kinds.contains(&(0x11e0, RefKind::Call)), "{kinds:?}");
    assert!(refs.windows(2).all(|w| w[0].1.va <= w[1].1.va), "{kinds:?}");
    assert!(a.refs_from(0x1).is_empty());
}

/// Functions of one instruction shape over different constants share a
/// shape class but not a clone class.
///
/// `SP1` and `SP2` differ only in their immediates.
#[test]
fn near_clones_share_a_shape_class() {
    let a = Analysis::compute(&fixture());
    let shapes = a.shapes_of(0x4990);
    assert!(
        shapes.contains(&0x4990) && shapes.contains(&0x49a0),
        "{shapes:?}"
    );
    assert!(a.clones_of(0x4990).is_empty());
    assert_ne!(
        a.function(0x4990).map(|f| f.body_hash),
        a.function(0x49a0).map(|f| f.body_hash)
    );
}

/// The function summary carries the effects line the decompile header has.
///
/// `LK` drops a count through an atomic on `a1 + 8`.
#[test]
fn function_summary_carries_effects() {
    use borer_engine::analysis::render::function_summary;
    let p = fixture();
    let a = Analysis::compute(&p);
    let s = function_summary(&p, &a, &Overlay::default(), 0x4790).expect("summary");
    assert!(s.contains("effects:  writes a1+8"), "{s}");
}

/// The function summary shows the comment the overlay holds at the entry,
/// and only that one: a comment inside the body stays with its
/// instruction.
///
/// `LK` gets a comment at its entry, then one at its second instruction.
#[test]
fn function_summary_shows_the_entry_comment() {
    use borer_engine::analysis::render::function_summary;
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.comments.insert(0x4791, "inside the body".to_owned());
    let s = function_summary(&p, &a, &o, 0x4790).expect("summary");
    assert!(!s.contains("comment:"), "{s}");
    o.comments.insert(0x4790, "? drops a reference".to_owned());
    let s = function_summary(&p, &a, &o, 0x4790).expect("summary");
    let range = s.lines().position(|l| l.starts_with("range:"));
    let comment = s.lines().position(|l| l == "comment:  ? drops a reference");
    assert_eq!(comment, range.map(|r| r + 1), "{s}");
}

/// Overrides of one virtual method share its return verdict.
///
/// `CB` reads the result of `BF1`, so slot 1 of `class_2970` returns a
/// value; `DF1` overrides that slot in `class_2988`, whose parent is
/// `class_2970`, and has no caller, so it takes the verdict.
#[test]
fn slot_siblings_share_the_return_verdict() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let verdict = |e: u64| a.function(e).and_then(|f| f.returns_value);
    assert_eq!(verdict(0x1de0), Some(true));
    assert_eq!(verdict(0x1df0), Some(true));
    assert_eq!(
        a.classes
            .by_name
            .get("class_2988")
            .and_then(|c| c.parent.as_deref()),
        Some("class_2970")
    );
}

/// A field filled by a creator and the getter of that field carry the
/// class.
///
/// `DK3` stores `DC`'s result at `this + 8`, so `class_2910`'s field at 8
/// holds a `Ns::Thing`; `FG`, slot 2 of `class_2910`, returns that field,
/// so it returns a `Ns::Thing`.
#[test]
fn creator_filled_fields_and_their_getters_carry_the_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes
            .field_hints
            .get(&("class_2910".to_owned(), 8))
            .map(String::as_str),
        Some("Ns::Thing")
    );
    assert_eq!(
        a.function(0x1c50).and_then(|f| f.ret_hint.as_deref()),
        Some("Ns::Thing")
    );
}

/// A constructor this pass names still registers its singleton.
///
/// `DK3` stores the table at 0x2910, which nothing names, and stores `this`
/// at 0x3010; the class `class_2910` gets that global as its singleton.
#[test]
fn constructors_named_by_the_pass_register_singletons() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let c = a.classes.by_name.get("class_2910").expect("class_2910");
    assert_eq!(c.ctors, vec![0x1c30]);
    assert_eq!(
        a.classes.global_hints.get(&0x3010).map(String::as_str),
        Some("class_2910")
    );
}

/// Creators, the globals they fill and the getters of those globals carry
/// the class along.
///
/// `DC` returns the result of `DK`, a constructor of `Ns::Thing`, so it
/// returns a `Ns::Thing`; `GS` stores `DC`'s result at 0x3008, so the global
/// holds one; `GG` returns the global's word, so it returns one too.
#[test]
fn creators_globals_and_getters_carry_the_class() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let hint = |e: u64| a.function(e).and_then(|f| f.ret_hint.as_deref());
    assert_eq!(hint(0x1bc0), Some("Ns::Thing"));
    assert_eq!(
        a.classes.global_hints.get(&0x3008).map(String::as_str),
        Some("Ns::Thing")
    );
    assert_eq!(hint(0x1c10), Some("Ns::Thing"));
}

/// A constructor with its base's constructor inlined stores two tables: the
/// shorter is the base's, the longer its own.
///
/// `TT` stores the two-slot table at 0x2a00 and then the three-slot table at
/// 0x2a20 without calling anything, so it constructs the class of the
/// longer table, whose parent owns the shorter.
#[test]
fn inlined_base_constructors_store_two_tables() {
    let a = Analysis::compute(&fixture());
    let own = a
        .classes
        .vtables
        .get(&0x2a20)
        .expect("derived table")
        .clone();
    let base = a.classes.vtables.get(&0x2a00).expect("base table").clone();
    let c = a.classes.by_name.get(&own).expect("derived class");
    assert_eq!(c.parent.as_deref(), Some(base.as_str()));
    assert_eq!(c.ctors, vec![0x1e50]);
    assert_eq!(
        a.function(0x1e50).and_then(|f| f.name.clone()),
        Some(format!("{own}::ctor_or_dtor"))
    );
}

/// An initializer names the descriptor of a class no registration spells.
///
/// `DI3` spells `"Ns::T3"` beside the unnamed object at 0x3080 and the
/// named `Ns::Thing` descriptor, so the object is `Ns::T3`'s and its parent
/// is `Ns::Thing`.
#[test]
fn initializers_name_unregistered_descriptors() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T3").expect("Ns::T3");
    assert_eq!(c.parent.as_deref(), Some("Ns::Thing"));
}

/// A constructor storing three tables in order names the longest its own
/// and the next its parent's.
///
/// `TT3` stores the two-, three- and four-slot tables at 0x2a00, 0x2a20 and
/// 0x2ab0 in turn: it constructs the class of the four-slot table, whose
/// parent owns the three-slot one (`TT`'s class), the base of that base
/// having been inlined too.
#[test]
fn three_inlined_tables_name_the_nearest_base() {
    let a = Analysis::compute(&fixture());
    let own = a.classes.vtables.get(&0x2ab0).expect("own table").clone();
    let mid = a
        .classes
        .vtables
        .get(&0x2a20)
        .expect("middle table")
        .clone();
    let c = a.classes.by_name.get(&own).expect("class");
    assert_eq!(c.parent.as_deref(), Some(mid.as_str()));
    assert_eq!(c.ctors, vec![0x10e1]);
}

/// A creator constructing in place gives a descriptor-only class its
/// vtable.
///
/// `CI` stores the table at 0x2ad8 through the allocation a call returned
/// and references `Ns::T3`'s descriptor: `Ns::T3`, known until now only
/// from its descriptor, owns that table, keeps its descriptor parent, and
/// `CI` is its `create`.
#[test]
fn creators_constructing_in_place_give_classes_their_vtable() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T3").expect("Ns::T3");
    assert_eq!(c.vtable, Some(0x2ad8));
    assert_eq!(c.parent.as_deref(), Some("Ns::Thing"));
    assert_eq!(c.creators, vec![0x11e4]);
    assert_eq!(
        a.function(0x11e4).and_then(|f| f.name.as_deref()),
        Some("Ns::T3::create")
    );
}

/// The parent a class's descriptor names wins over the base table its
/// constructor stores first.
///
/// `TT2` stores the two-slot table at 0x2a00 before its own at 0x2a60, and
/// `CR` creates from the descriptor `DR4` registers as `Ns::T4`, whose
/// initializer `DI4` names `Ns::T2` as the parent: the class is `Ns::T4`
/// with parent `Ns::T2`, not the class of the inlined table, since a store
/// the compiler kept may be a grandparent's.
#[test]
fn descriptor_parents_win_over_inlined_tables() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T4").expect("Ns::T4");
    assert_eq!(c.vtable, Some(0x2a60));
    assert_eq!(c.parent.as_deref(), Some("Ns::T2"));
}

/// Slot sharing walks through ancestors without a table.
///
/// `Ns::T4` derives from `Ns::T2`, a class known only from its descriptor,
/// which derives from `Ns::Thing`: slot 1 of `Ns::T4`'s table (`BF1`, whose
/// result `CB` reads) and slot 1 of `Ns::Thing`'s (`S4`, which nothing
/// calls) override one method, so `S4` takes the verdict.
#[test]
fn slot_sharing_walks_through_classes_without_a_table() {
    let a = Analysis::compute(&fixture());
    assert_eq!(
        a.classes
            .by_name
            .get("Ns::T2")
            .and_then(|c| c.parent.as_deref()),
        Some("Ns::Thing")
    );
    assert_eq!(a.function(0x1bf0).and_then(|f| f.returns_value), Some(true));
}

/// Creators voting several descriptors name the table after their common
/// ancestor.
///
/// `DC` creates from `Ns::Thing`'s descriptor and `DC3` from `Ns::T2`'s,
/// both calling `DK`; `Ns::T2` derives from `Ns::Thing`, so the table `DK`
/// stores is `Ns::Thing`'s.
#[test]
fn conflicting_creator_votes_resolve_to_the_common_ancestor() {
    let a = Analysis::compute(&fixture());
    assert_eq!(
        a.classes.vtables.get(&0x28c0).map(String::as_str),
        Some("Ns::Thing")
    );
    assert_eq!(
        a.function(0x1050).map(|f| f.callees.clone()),
        Some(vec![0x1bb0])
    );
}

/// A descriptor initializer links a class to its parent.
///
/// `DI` spells `"Ns::T2"` beside two described objects, the one `DR2`
/// registered under that name and `Ns::Thing`'s, so `Ns::T2` derives from
/// `Ns::Thing`; no constructor stores a table for it, so it is a class
/// without a vtable.
#[test]
fn descriptor_initializers_link_parents() {
    let a = Analysis::compute(&fixture());
    let c = a.classes.by_name.get("Ns::T2").expect("Ns::T2");
    assert_eq!(c.parent.as_deref(), Some("Ns::Thing"));
    assert_eq!(c.vtable, None);
    assert!(
        a.classes
            .by_name
            .get("Ns::Thing")
            .is_some_and(|t| t.parent.is_none())
    );
}

/// A table no signature names takes its class name from the descriptor its
/// creator allocates from.
///
/// `DR` spells `"Ns::Thing"` beside the object at 0x3000, `DC` references
/// that object and calls `DK`, which stores the table at 0x28c0, so the
/// table is `Ns::Thing`'s and `DK` its `ctor_or_dtor`.
#[test]
fn descriptors_name_constructed_tables() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes.vtables.get(&0x28c0).map(String::as_str),
        Some("Ns::Thing")
    );
    let c = a.classes.by_name.get("Ns::Thing").expect("Ns::Thing");
    assert_eq!(c.slots, vec![0x1be0, 0x1bf0]);
    assert_eq!(c.ctors, vec![0x1bb0]);
    assert_eq!(
        a.function(0x1bb0).and_then(|f| f.name.as_deref()),
        Some("Ns::Thing::ctor_or_dtor")
    );
    assert!(!a.classes.by_name.contains_key("class_28c0"));
}

/// A table nothing names but a function stores at `[this]` is a class of
/// its own.
///
/// `UT` stores the table at 0x2800, so `class_2800` exists with the table's
/// slots, `UT` is its `ctor_or_dtor` and its slot functions take it as
/// `this`.
#[test]
fn unnamed_tables_with_a_constructor_become_classes() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes.vtables.get(&0x2800).map(String::as_str),
        Some("class_2800")
    );
    let c = a.classes.by_name.get("class_2800").expect("class_2800");
    assert_eq!(c.slots, vec![0x1b20, 0x1b30]);
    assert_eq!(c.ctors, vec![0x1b10]);
    let ut = a.function(0x1b10).expect("UT");
    assert_eq!(ut.name.as_deref(), Some("class_2800::ctor_or_dtor"));
    let s1 = a.function(0x1b20).expect("S1");
    assert_eq!(
        s1.param_hints.get(&0).map(String::as_str),
        Some("class_2800")
    );
}

/// A table no named constructor stores is named by its slots.
///
/// 0x22c0 holds `Der2::Foo` (in no other table) and a shared slot, so it is
/// `Der2`'s vtable; the unnamed function storing it becomes
/// `Der2::ctor_or_dtor` and its base-constructor call makes `Der` the parent.
#[test]
fn tables_without_constructors_are_named_by_their_slots() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let der2 = a.classes.by_name.get("Der2").expect("Der2");
    assert_eq!(der2.vtable, Some(0x22c0));
    assert_eq!(der2.slots, vec![0x1740, 0x1200]);
    assert_eq!(der2.parent.as_deref(), Some("Der"));
    assert_eq!(der2.ctors, vec![0x1750]);
    assert_eq!(
        a.classes.vtables.get(&0x22c0).map(String::as_str),
        Some("Der2")
    );
    let uc2 = a.function(0x1750).expect("UC2");
    assert_eq!(uc2.name.as_deref(), Some("Der2::ctor_or_dtor"));
}

/// The layout of `Cls` lists its fields with widths, directions and types.
///
/// `Cls::Set` reads field 0, writes fields 8 (32-bit) and 0x10 (64-bit) and
/// passes `this + 0x20` to the `const` method `Other::Get`, so the embedded
/// `Other` at 0x20 is typed, and the rendering names the methods. `IG`
/// hands its first argument to `Cls::Has` as `this`, so it takes a `Cls` and
/// counts among the functions of the class.
#[test]
fn class_layout_collects_field_accesses_of_the_methods() {
    use borer_engine::analysis::classes::{class_layout, methods_of, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(methods_of(&a, &o, "Cls"), vec![0x1640, 0x1660, 0x40f4]);
    let layout = class_layout(&p, &a, &o, "Cls").expect("class found");
    let text = borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1640).expect("text");
    let f0 = layout.fields.get(&0).expect("field 0");
    assert!(f0.reads >= 1 && f0.writes == 0, "{text}");
    assert!(f0.widths.contains(&64));
    let f8 = layout.fields.get(&8).expect("field 8");
    assert_eq!((f8.reads, f8.writes), (1, 1));
    assert!(f8.widths.contains(&32));
    let f10 = layout.fields.get(&0x10).expect("field 0x10");
    assert_eq!((f10.reads, f10.writes), (0, 1));
    let text = render_layout(&layout, &a, &o);
    assert!(
        text.starts_with("class Cls: 3 methods, 4 fields, size >= 0x28"),
        "{text}"
    );
    assert!(text.contains("+0x8    u32        1/1   Set, Has"), "{text}");
    let f20 = layout.fields.get(&0x20).expect("field 0x20");
    assert!(f20.types.contains("Other"), "{text}");
    assert_eq!(f20.address_taken, 1);
    assert!(text.contains("+0x20   Other"), "{text}");
}

/// A linear sweep stops where the containing function's code stops.
///
/// `T` is a two-instruction import thunk; the bytes after it belong to the
/// next function, not to this one, so a sweep that starts at `T` must not
/// run on into them.
#[test]
fn a_sweep_stops_at_the_end_of_its_function() {
    let a = Analysis::compute(&fixture());
    let f = a.function(0x1210).expect("T is a function");
    assert_eq!(
        borer_engine::analysis::render::sweep_limit(&a, 0x1210),
        Some(f.end)
    );
    assert_eq!(
        borer_engine::analysis::render::sweep_limit(&a, 0x2040),
        None
    );
}

/// A call through an import slot names the import in the disassembly.
///
/// `call qword [rel <slot>]` reaches an import without a thunk, and the slot
/// address is the only thing that says which one. Left as a number, every
/// such call reads as a branch into data.
#[test]
fn disassembly_names_the_import_a_slot_call_reaches() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let out = borer_engine::analysis::render::disasm_function(
        &p,
        &a,
        &Overlay::default(),
        0x1810,
        64,
        false,
    )
    .expect("AS disassembles");
    assert!(out.contains("KERNEL32.dll!ReportAssertFailure"), "{out}");
}

/// The oracle runs a function and reports what it returned.
///
/// A constant table says which algorithm a function resembles; running it on
/// the published probe says which algorithm it is. On a real binary this
/// turns "a table matching CRC-32C is present" into "this function returns
/// the CRC-32C check value".
#[test]
fn the_oracle_runs_a_function_and_reports_its_result() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = borer_engine::analysis::render::oracle_tsv(&p, &a, &o, "0x1810").unwrap();
    assert!(out.contains("# ran "), "{out}");
    assert!(out.contains("rax "), "{out}");
    let missing = borer_engine::analysis::render::oracle_tsv(&p, &a, &o, "0xdeadbeef").unwrap_err();
    assert!(missing.contains("no discovered function"), "{missing}");
}

/// A function that returns in no argument shape is reported once per shape.
///
/// The table listed the first four of the eight tries, a strict and a
/// lenient run per shape, so two shapes appeared twice and two not at all;
/// its header promises one outcome per shape. `NR` spins at `jmp $`, so
/// every try runs out of budget.
#[test]
fn the_oracle_lists_each_failed_shape_once() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = borer_engine::analysis::render::oracle_tsv(&p, &a, &o, "0x12b0").unwrap();
    assert!(out.contains("did not run to a return"), "{out}");
    let shapes: Vec<&str> = out
        .lines()
        .filter(|l| !l.starts_with('#'))
        .map(|l| l.get(..22).map_or(l, str::trim_end))
        .collect();
    assert_eq!(
        shapes,
        [
            "buffer, length",
            "length, buffer",
            "buffer",
            "this, buffer, length"
        ],
        "{out}"
    );
}

/// A class layout, applied, defines its struct and types each method's
/// object with it, so the re-decompiled methods name the fields.
///
/// `Cls` reads a qword at 0, a dword at 8 and writes a qword at 0x10, and
/// hands the address of an embedded `Other` at 0x20 on: the struct takes
/// the three, notes the embedded one it cannot size, and every method's
/// first parameter becomes a `ClsS *`.
#[test]
fn an_applied_class_layout_types_each_methods_object() {
    use borer_engine::analysis::apply::from_class;
    use borer_engine::analysis::classes::class_layout;
    let p = fixture();
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let layout = class_layout(&p, &a, &plain, "Cls").expect("class found");
    let plan = from_class(&p, &a, &plain, &layout, "ClsS").expect("a plan");
    assert_eq!(
        plan.describe(&a, &plain),
        [
            "struct ClsS (0x18 bytes): 0x0 f_0 u64, 0x8 f_8 u32, 0x10 f_10 u64",
            "prototype Cls::Set (0x1640): void (ClsS *this, int)",
            "prototype Cls::Has (0x1660): bool (ClsS *this, int)",
            "prototype sub_40f4 (0x40f4): uint32_t (ClsS *)",
            "# 0x20 is only addressed (an embedded object), so it states no width; left out",
        ]
    );
    let before =
        borer_engine::analysis::decompile::decompile(&p, &a, &plain, 0x1640).expect("text");
    assert!(before.contains("this->field_0x8 = a2;"), "{before}");
    let mut o = plain;
    plan.apply(&mut o);
    let set = borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1640).expect("text");
    assert!(
        set.contains("// signature: void Cls::Set(ClsS *this, int a2)"),
        "{set}"
    );
    assert!(set.contains("this->f_8 = a2;"), "{set}");
    assert!(set.contains("this->f_10 = "), "{set}");
}

/// File-backed sections that overlap or share a start answer a read by
/// declaration order.
///
/// The first-declared section that holds the address answers, both for
/// `section_at` and for the bytes `read_va` returns, and the address only
/// the second section spans still reads the second's. `section_at` walks
/// an address-ordered index, and the walk must keep the linear scan's
/// answer - the first section in file order - wherever sections nest or
/// share a virtual address, so a read that lands on the overlap still
/// returns the bytes of the section declared first.
///
/// # Panics
///
/// When the wrong section answers or its bytes come back.
#[test]
fn overlapping_sections_answer_in_declaration_order() {
    let mut bytes = vec![0xaau8; 0x200];
    bytes.extend(vec![0xbbu8; 0x300]);
    let p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        None,
        vec![
            Section::mapped(".first", 0x1000, 0, 0x200, false, false),
            Section::mapped(".second", 0x1100, 0x200, 0x300, false, false),
        ],
    );
    assert_eq!(
        p.section_at(0x1000).map(|s| s.name.as_str()),
        Some(".first")
    );
    assert_eq!(
        p.section_at(0x1100).map(|s| s.name.as_str()),
        Some(".first")
    );
    assert_eq!(p.read_va(0x1100, 4), Some(&[0xaa, 0xaa, 0xaa, 0xaa][..]));
    assert_eq!(
        p.section_at(0x1200).map(|s| s.name.as_str()),
        Some(".second")
    );
    assert_eq!(p.read_va(0x1200, 4), Some(&[0xbb, 0xbb, 0xbb, 0xbb][..]));
    assert!(p.section_at(0x1400).is_none());
    let tied = Program::raw(
        vec![0x11, 0x22, 0x33, 0x44],
        Arch::X86_64,
        0,
        None,
        vec![
            Section::mapped(".a", 0x1000, 0, 0x2, false, false),
            Section::mapped(".b", 0x1000, 0x2, 0x2, false, false),
        ],
    );
    assert_eq!(tied.section_at(0x1000).map(|s| s.name.as_str()), Some(".a"));
    assert_eq!(tied.read_va(0x1000, 2), Some(&[0x11, 0x22][..]));
}
