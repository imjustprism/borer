//! References, call paths, the call graph and the summaries built on them.

use super::*;

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
    let out = borer_engine::analysis::render::xrefs_tsv(&p, &a, &o, 0x2040, 0, 60, false);
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
        borer_engine::analysis::render::xrefs_tsv(&p, &a, &Overlay::default(), 0x2040, 0, 60, true);
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

/// The cross-reference listing spells each site's kind as the word it
/// always printed, so a typed kind changes no answer.
#[test]
fn an_xrefs_row_spells_each_site_kind() {
    let (p, o) = (fixture(), Overlay::default());
    let a = Analysis::compute(&p);
    let out = borer_engine::analysis::render::xrefs_tsv(&p, &a, &o, 0x2050, 0, 60, false);
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
    let refs = xrefs_tsv(&p, &a, &o, 0x2040, 0, 60, false);
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
