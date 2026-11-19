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
        has.contains("declared: bool Cls::Has(int) const; from a signature string the function references (its own body, code inlined from it, or code handed the string)\n"),
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

/// Builds an image whose `f` 0x401000 makes one call of each kind the
/// call tree tells apart.
///
/// * `f` 0x401000: `call g; call [Sleep]; call thunk; ret`.
/// * `g` 0x401020: `mov eax, 1; ret`.
/// * `thunk` 0x401030: `jmp [ExitProcess]`.
///
/// The import slots are `Sleep` at 0x402000 and `ExitProcess` at 0x402008.
fn call_tree_image() -> Program {
    let mut code = vec![0xccu8; 0x40];
    code[..5].copy_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00]); // ASM: call 0x401020
    code[5..11].copy_from_slice(&[0xff, 0x15, 0xf5, 0x0f, 0x00, 0x00]); // ASM: call [rip+0xff5] -> 0x402000
    code[11..16].copy_from_slice(&[0xe8, 0x20, 0x00, 0x00, 0x00]); // ASM: call 0x401030
    code[16] = 0xc3; // ASM: ret
    code[0x20..0x26].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    code[0x30..0x36].copy_from_slice(&[0xff, 0x25, 0xd2, 0x0f, 0x00, 0x00]); // ASM: jmp [rip+0xfd2] -> 0x402008
    let mut p = crate::raw::image(Arch::X86_64, &code, &[0; 0x10]);
    p.symbols = vec![
        Symbol {
            name: "KERNEL32.dll!Sleep".to_owned(),
            addr: 0x402000,
            kind: SymbolKind::Import,
        },
        Symbol {
            name: "KERNEL32.dll!ExitProcess".to_owned(),
            addr: 0x402008,
            kind: SymbolKind::Import,
        },
    ];
    p
}

/// One level of the call tree says how each call is known and where it
/// is made.
///
/// A direct call, a call through an import slot and a call of an import
/// thunk are three edges of three kinds, each with its site.
#[test]
fn a_call_tree_level_says_how_each_callee_is_reached() {
    use borer_engine::analysis::render::{Level, Via, call_children};
    let p = call_tree_image();
    let a = Analysis::compute(&p);
    let level = call_children(&p, &a, &Overlay::default(), 0x401000, Level::Callees);
    let got: Vec<(u64, Via, &[u64], bool)> = level
        .rows
        .iter()
        .map(|e| (e.target, e.via, e.sites.as_slice(), e.leaf))
        .collect();
    assert_eq!(
        got,
        [
            (0x401020, Via::Direct, &[0x401000][..], true),
            (
                0x401030,
                Via::Thunk { slot: 0x402008 },
                &[0x40100b][..],
                false
            ),
            (0x402000, Via::Import, &[0x401005][..], true),
        ],
        "{level:?}"
    );
    assert_eq!(level.total, 3, "{level:?}");
    assert_eq!(&*level.rows[2].name, "Sleep", "{level:?}");
}

/// Over callers a level names the calling function and the instruction in
/// it that makes the call, and says how the call reaches the node.
#[test]
fn a_call_tree_level_over_callers_names_each_call_site() {
    use borer_engine::analysis::render::{Level, Via, call_children};
    let p = call_tree_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for (node, via, site) in [
        (0x401020, Via::Direct, 0x401000),
        (0x401030, Via::Thunk { slot: 0x402008 }, 0x40100b),
        (0x402000, Via::Import, 0x401005),
    ] {
        let level = call_children(&p, &a, &o, node, Level::Callers);
        let got: Vec<(u64, Via, &[u64], bool)> = level
            .rows
            .iter()
            .map(|e| (e.target, e.via, e.sites.as_slice(), e.leaf))
            .collect();
        assert_eq!(
            got,
            [(0x401000, via, &[site][..], true)],
            "{node:#x}: {level:?}"
        );
    }
}

/// Returns the instruction starts of a function, decoded block by block.
///
/// # Arguments
///
/// * `p` - The image.
/// * `f` - The function.
fn instruction_starts(p: &Program, f: &borer_engine::analysis::Function) -> Option<Vec<u64>> {
    let mut out = Vec::new();
    for b in &f.blocks {
        let len = usize::try_from(b.end.checked_sub(b.start)?).ok()?;
        let bytes = p.read_va(b.start, len)?;
        let mut d = iced_x86::Decoder::with_ip(64, bytes, b.start, iced_x86::DecoderOptions::NONE);
        while d.can_decode() {
            out.push(d.decode().ip());
        }
    }
    Some(out)
}

/// Returns the address a call or jump names: its near target, or the
/// memory it goes through.
///
/// # Arguments
///
/// * `p` - The image.
/// * `site` - The instruction's address.
fn named_by(p: &Program, site: u64) -> Option<u64> {
    let bytes = p.read_va_upto(site, 15)?;
    let i = iced_x86::Decoder::with_ip(64, bytes, site, iced_x86::DecoderOptions::NONE).decode();
    Some(if i.op0_kind() == iced_x86::OpKind::Memory {
        i.memory_displacement64()
    } else {
        i.near_branch_target()
    })
}

/// Builds an image whose `C` 0x401000 calls a linkage stub bound to a
/// local function and calls through an import slot that `H` only loads.
///
/// * `C` 0x401000: `call S; call [Sleep]; ret`.
/// * `H` 0x401010 (an export): `mov rax, [Sleep]; ret`.
/// * `F` 0x401020 (the export `local_f`): `mov eax, 1; ret`.
/// * `S` 0x401030: `jmp [0x402010]`, the slot holding `F`'s entry.
/// * `K` 0x401040 (an export): `mov rax, [Sleep]; call [Sleep]; ret`.
///
/// The import slot `Sleep` is at 0x402000.
fn bound_stub_image() -> Program {
    let mut code = vec![0xccu8; 0x50];
    code[..5].copy_from_slice(&[0xe8, 0x2b, 0x00, 0x00, 0x00]); // ASM: call 0x401030
    code[5..11].copy_from_slice(&[0xff, 0x15, 0xf5, 0x0f, 0x00, 0x00]); // ASM: call [rip+0xff5] -> 0x402000
    code[11] = 0xc3; // ASM: ret
    code[0x10..0x17].copy_from_slice(&[0x48, 0x8b, 0x05, 0xe9, 0x0f, 0x00, 0x00]); // ASM: mov rax,[rip+0xfe9] -> 0x402000
    code[0x17] = 0xc3; // ASM: ret
    code[0x20..0x26].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    code[0x30..0x36].copy_from_slice(&[0xff, 0x25, 0xda, 0x0f, 0x00, 0x00]); // ASM: jmp [rip+0xfda] -> 0x402010
    code[0x40..0x47].copy_from_slice(&[0x48, 0x8b, 0x05, 0xb9, 0x0f, 0x00, 0x00]); // ASM: mov rax,[rip+0xfb9] -> 0x402000
    code[0x47..0x4d].copy_from_slice(&[0xff, 0x15, 0xb3, 0x0f, 0x00, 0x00]); // ASM: call [rip+0xfb3] -> 0x402000
    code[0x4d] = 0xc3; // ASM: ret
    let mut data = [0u8; 0x18];
    data[0x10..].copy_from_slice(&0x401020u64.to_le_bytes());
    let mut p = crate::raw::image(Arch::X86_64, &code, &data);
    p.symbols = vec![
        Symbol {
            name: "KERNEL32.dll!Sleep".to_owned(),
            addr: 0x402000,
            kind: SymbolKind::Import,
        },
        Symbol {
            name: "h".to_owned(),
            addr: 0x401010,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "local_f".to_owned(),
            addr: 0x401020,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "k".to_owned(),
            addr: 0x401040,
            kind: SymbolKind::Export,
        },
    ];
    p
}

/// A call to a stub the loader binds to a local function is an edge to
/// that function both ways.
///
/// Only a call through an import slot makes a caller of the slot an
/// import call: a load of the slot is a data reference, and a function
/// that loads the slot and calls through it lists the call alone.
#[test]
fn a_call_tree_level_follows_a_bound_stub_and_tells_a_load_from_a_call() {
    use borer_engine::analysis::render::{Level, Via, call_children};
    let p = bound_stub_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let level = |node, level| -> Vec<(u64, Via, Vec<u64>, usize)> {
        call_children(&p, &a, &o, node, level)
            .rows
            .into_iter()
            .map(|e| {
                assert!(e.leaf, "{e:?}");
                (e.target, e.via, e.sites, e.site_count)
            })
            .collect()
    };
    let bound = Via::Bound { stub: 0x401030 };
    assert_eq!(
        level(0x401000, Level::Callees),
        [
            (0x401020, bound, vec![0x401000], 1),
            (0x402000, Via::Import, vec![0x401005], 1),
        ]
    );
    assert_eq!(
        level(0x401020, Level::Callers),
        [(0x401000, bound, vec![0x401000], 1)]
    );
    assert_eq!(
        level(0x402000, Level::Callers),
        [
            (0x401000, Via::Import, vec![0x401005], 1),
            (0x401010, Via::Data, vec![0x401010], 1),
            (0x401040, Via::Import, vec![0x401047], 1),
        ]
    );
}

/// An edge made by more calls than it lists says how many there are.
///
/// `f` 0x401000 calls `g` 0x401060 seventeen times, then returns.
#[test]
fn a_call_tree_edge_counts_the_sites_it_leaves_out() {
    use borer_engine::analysis::render::{CALL_SITES_MAX, Level, call_children};
    let mut code = vec![0xccu8; 0x61];
    for k in 0..17u8 {
        let at = usize::from(k) * 5;
        let rel = 0x5b - i32::from(k) * 5;
        code[at] = 0xe8; // ASM: call 0x401060
        code[at + 1..at + 5].copy_from_slice(&rel.to_le_bytes());
    }
    code[0x55] = 0xc3; // ASM: ret
    code[0x60] = 0xc3; // ASM: ret (g)
    let p = crate::raw::image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for (node, level) in [(0x401000, Level::Callees), (0x401060, Level::Callers)] {
        let level = call_children(&p, &a, &o, node, level);
        let [e] = level.rows.as_slice() else {
            panic!("one edge: {level:?}");
        };
        assert_eq!((e.sites.len(), e.site_count), (CALL_SITES_MAX, 17), "{e:?}");
        assert_eq!(e.sites.first(), Some(&0x401000), "{e:?}");
    }
}

/// Every edge a level lists over a function has its sites, each a call
/// in the caller.
///
/// Each site is an instruction of the calling function naming the called
/// end, never the callee's entry; a resolved virtual call names a vtable
/// slot, so it is only held to being a call. Each edge says it is a leaf
/// exactly when its target's own level is empty. Every level runs, on
/// every function of the fixture and of the call tree images.
#[test]
fn every_call_tree_site_is_a_call_in_the_caller() {
    use borer_engine::analysis::render::{Level, Via, call_children};
    let mut checked = 0;
    for p in [fixture(), call_tree_image(), bound_stub_image()] {
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        for f in &a.functions {
            for level in [Level::Callees, Level::CalleesAndVirtuals, Level::Callers] {
                let next_level = match level {
                    Level::Callers => Level::Callers,
                    Level::Callees | Level::CalleesAndVirtuals => Level::Callees,
                };
                for e in call_children(&p, &a, &o, f.entry, level).rows {
                    let (caller, called) = match (next_level, e.via) {
                        (Level::Callers, Via::Bound { stub }) => (e.target, Some(stub)),
                        (Level::Callers, _) => (e.target, Some(f.entry)),
                        (_, Via::Virtual { .. }) => (f.entry, None),
                        (_, Via::Bound { stub }) => (f.entry, Some(stub)),
                        (_, _) => (f.entry, Some(e.target)),
                    };
                    assert!(!e.sites.is_empty(), "{:#x}: no site for {e:?}", f.entry);
                    assert!(e.site_count >= e.sites.len(), "{e:?}");
                    let next = call_children(&p, &a, &o, e.target, next_level);
                    assert_eq!(e.leaf, next.total == 0, "{e:?}: {next:?}");
                    let g = a.function(caller).expect("the caller is a function");
                    let starts = instruction_starts(&p, g).expect("the caller's bytes");
                    for &s in &e.sites {
                        assert!(
                            starts.contains(&s),
                            "{s:#x} is no instruction of {caller:#x}"
                        );
                        match called {
                            Some(c) => assert_eq!(named_by(&p, s), Some(c), "{s:#x}: {e:?}"),
                            None => assert!(is_call(&p, s), "{s:#x} is no call: {e:?}"),
                        }
                        checked += 1;
                    }
                }
            }
        }
    }
    assert!(checked > 10, "only {checked} sites checked");
}

/// Tells whether the instruction at an address is a call.
///
/// # Arguments
///
/// * `p` - The image.
/// * `site` - The instruction's address.
fn is_call(p: &Program, site: u64) -> bool {
    p.read_va_upto(site, 15).is_some_and(|bytes| {
        let i =
            iced_x86::Decoder::with_ip(64, bytes, site, iced_x86::DecoderOptions::NONE).decode();
        matches!(
            i.flow_control(),
            iced_x86::FlowControl::Call | iced_x86::FlowControl::IndirectCall
        )
    })
}

/// A virtual call is an edge only when asked for, and then with its slot
/// and its site: `VR` calls slot 1 of `this`'s vtable at 0x1773, which
/// resolves to 0x1200, a call no cross-reference records.
#[test]
fn a_call_tree_level_lists_a_virtual_call_only_when_asked() {
    use borer_engine::analysis::render::{Level, Via, call_children};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let virtual_rows = |level| -> Vec<(u64, Via, Vec<u64>)> {
        call_children(&p, &a, &o, 0x1770, level)
            .rows
            .into_iter()
            .filter(|e| matches!(e.via, Via::Virtual { .. }))
            .map(|e| (e.target, e.via, e.sites))
            .collect()
    };
    assert_eq!(virtual_rows(Level::Callees), []);
    assert_eq!(
        virtual_rows(Level::CalleesAndVirtuals),
        [(0x1200, Via::Virtual { slot: 1 }, vec![0x1773])]
    );
}

/// Returns the graph a typed graph was laid out from: each node a box one
/// row high and its name wide, plus a cell on every side, and each edge
/// down from its `from` to its `to`, a back edge up the side.
///
/// # Arguments
///
/// * `g` - The typed graph.
/// * `name` - Each node's name.
fn laid_from<N, E>(
    g: &borer_engine::analysis::render::TypedGraph<N, E>,
    name: impl Fn(&N) -> &str,
) -> borer_engine::analysis::render::Graph {
    use borer_engine::analysis::render::{Graph, GraphEdge, Route};
    let cells = |n: &N| u32::try_from(name(n).chars().count() + 2).unwrap_or(u32::MAX);
    Graph {
        sizes: g.nodes.iter().map(|n| (cells(n), 3)).collect(),
        edges: g
            .edges
            .iter()
            .map(|e| GraphEdge {
                from: e.from,
                to: e.to,
                route: if e.back { Route::Up } else { Route::Down },
            })
            .collect(),
        root: g.root,
    }
}

/// Checks a typed graph's drawing: the drawing rules hold over its edges
/// from `from` to `to`, and every edge but a back edge goes down.
///
/// # Arguments
///
/// * `g` - The typed graph.
/// * `name` - Each node's name.
fn drawn_down<N, E>(
    g: &borer_engine::analysis::render::TypedGraph<N, E>,
    name: impl Fn(&N) -> &str,
) {
    let l = g.layout();
    assert_eq!(crate::drawn::check(&laid_from(g, name), &l), Ok(()));
    for e in g.edges.iter().filter(|e| !e.back) {
        assert!(
            l.at[e.from].1 < l.at[e.to].1,
            "edge {}->{} goes up",
            e.from,
            e.to
        );
    }
}

/// The calls around a function are a typed graph: each node an address
/// with its kind, each edge how the call is known and where it is made,
/// laid out under the drawing rules, built once.
///
/// One level under 0x401000 holds the thunk's call of `ExitProcess`, past
/// the depth, as an open node; two levels hold the import too.
#[test]
fn the_calls_around_a_function_are_a_typed_graph() {
    use borer_engine::analysis::render::{AddrKind, Via, Walk, call_graph};
    let p = call_tree_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let g = call_graph(&p, &a, &o, 0x401000, Walk::Callees, 2, 16);
    let nodes: Vec<(u64, &str, AddrKind, bool)> = g
        .nodes
        .iter()
        .map(|n| (n.addr, &*n.name, n.kind, n.open))
        .collect();
    let function = AddrKind::Function;
    assert_eq!(
        nodes,
        [
            (0x401000, "sub_401000", function, false),
            (0x401020, "sub_401020", function, false),
            (0x401030, "KERNEL32.dll!ExitProcess", function, false),
            (0x402000, "Sleep", AddrKind::Import, false),
            (0x402008, "ExitProcess", AddrKind::Import, false),
        ],
        "{g:?}"
    );
    let edges: Vec<(usize, usize, Via, &[u64])> = g
        .edges
        .iter()
        .map(|e| (e.from, e.to, e.kind.kind, e.kind.sites.as_slice()))
        .collect();
    assert_eq!(
        edges,
        [
            (0, 1, Via::Direct, &[0x401000][..]),
            (0, 2, Via::Thunk { slot: 0x402008 }, &[0x40100b][..]),
            (0, 3, Via::Import, &[0x401005][..]),
            (2, 4, Via::Import, &[0x401030][..]),
        ],
        "{g:?}"
    );
    assert_eq!((g.root, g.cut, g.incomplete), (0, None, false));
    drawn_down(&g, |n| &n.name);
    let again = call_graph(&p, &a, &o, 0x401000, Walk::Callees, 2, 16);
    assert!(std::sync::Arc::ptr_eq(&g, &again), "built once");
    let one = call_graph(&p, &a, &o, 0x401000, Walk::Callees, 1, 16);
    let open: Vec<(u64, bool)> = one.nodes.iter().map(|n| (n.addr, n.open)).collect();
    assert_eq!(
        open,
        [
            (0x401000, false),
            (0x401020, false),
            (0x401030, true),
            (0x402000, false)
        ],
        "{one:?}"
    );
    let cut = one.cut.expect("the import past the depth is counted");
    let counts = (cut.shown, cut.total, cut.edges_shown, cut.edges_total);
    assert_eq!(counts, (4, 5, 3, 4));
}

/// Over callers every edge still points the way calls go, down the drawing
/// to the root at the bottom; a cap cuts the nodes with a stated count;
/// a rename in force names the node anew.
#[test]
fn a_call_graph_over_callers_points_at_the_root_and_a_cap_says_what_it_cut() {
    use borer_engine::analysis::render::{Cut, Via, Walk, call_graph};
    let p = call_tree_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let g = call_graph(&p, &a, &o, 0x402000, Walk::Callers, 3, 16);
    let addrs: Vec<u64> = g.nodes.iter().map(|n| n.addr).collect();
    assert_eq!(addrs, [0x401000, 0x402000], "{g:?}");
    assert_eq!(g.root, 1);
    let edges: Vec<(usize, usize, Via)> = g
        .edges
        .iter()
        .map(|e| (e.from, e.to, e.kind.kind))
        .collect();
    assert_eq!(edges, [(0, 1, Via::Import)], "{g:?}");
    drawn_down(&g, |n| &n.name);
    let cut = call_graph(&p, &a, &o, 0x401000, Walk::Callees, 1, 2);
    let addrs: Vec<u64> = cut.nodes.iter().map(|n| n.addr).collect();
    assert_eq!(addrs, [0x401000, 0x401020], "{cut:?}");
    let want = Cut {
        shown: 2,
        total: 4,
        edges_shown: 1,
        edges_total: 3,
        shortened: 0,
    };
    assert_eq!(cut.cut, Some(want));
    drawn_down(&cut, |n| &n.name);
    let mut renamed = Overlay::default();
    renamed.names.insert(0x401020, "one".to_owned());
    let g = call_graph(&p, &a, &renamed, 0x401000, Walk::Callees, 1, 16);
    assert_eq!(&*g.nodes[1].name, "one", "{g:?}");
}

/// What references an address is a typed graph of what references it.
///
/// Each edge has its kind and sites and points at the target at the
/// bottom; an address inside a function, an import slot and one no section
/// maps say what they are.
#[test]
fn what_references_an_address_is_a_typed_graph() {
    use borer_engine::analysis::render::{AddrKind, xref_graph};
    let p = call_tree_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let g = xref_graph(&p, &a, &o, 0x401020, 2, 16);
    let nodes: Vec<(u64, AddrKind)> = g.nodes.iter().map(|n| (n.addr, n.kind)).collect();
    let function = AddrKind::Function;
    assert_eq!(nodes, [(0x401000, function), (0x401020, function)], "{g:?}");
    let edges: Vec<(usize, usize, RefKind, &[u64], usize)> = g
        .edges
        .iter()
        .map(|e| {
            let k = &e.kind;
            (e.from, e.to, k.kind, k.sites.as_slice(), k.site_count)
        })
        .collect();
    assert_eq!(edges, [(0, 1, RefKind::Call, &[0x401000][..], 1)], "{g:?}");
    assert_eq!((g.root, g.cut), (1, None));
    drawn_down(&g, |n| &n.name);
    let kind = |va: u64| {
        let g = xref_graph(&p, &a, &o, va, 1, 4);
        g.nodes.iter().find(|n| n.addr == va).map(|n| n.kind)
    };
    let alone = xref_graph(&p, &a, &o, 0x401020, 2, 1);
    let cut = alone.cut.expect("the referrer past the cap is counted");
    let counts = (alone.nodes.len(), cut.total, cut.edges_total);
    assert_eq!(counts, (1, 2, 1), "{alone:?}");
    assert_eq!(kind(0x401005), Some(AddrKind::Code));
    assert_eq!(kind(0x90_0000), Some(AddrKind::Unmapped));
    assert_eq!(kind(0x402000), Some(AddrKind::Import));
}

/// A call graph, a reference graph and their drawings come out the same
/// over two analyses and with the analysis run on one worker or sixteen.
#[test]
fn typed_graphs_draw_the_same_at_any_worker_count() {
    use borer_engine::analysis::render::{Walk, call_graph, xref_graph};
    use borer_engine::progress::Workers;
    let p = call_tree_image();
    let o = Overlay::default();
    let digests = |a: &Analysis| {
        let calls = call_graph(&p, a, &o, 0x401000, Walk::Callees, 4, 64);
        let refs = xref_graph(&p, a, &o, 0x402000, 4, 64);
        (
            crate::drawn::digest(&laid_from(&calls, |n| &n.name), &calls.layout()),
            crate::drawn::digest(&laid_from(&refs, |n| &n.name), &refs.layout()),
            format!("{:?}{:?}", calls.nodes, refs.edges),
        )
    };
    let want = digests(&Analysis::compute(&p));
    assert_eq!(digests(&Analysis::compute(&p)), want);
    for n in [1, 16] {
        let count = std::num::NonZeroUsize::new(n).unwrap_or(std::num::NonZeroUsize::MIN);
        let a = Workers(count).within(|| Analysis::compute(&p));
        assert_eq!(digests(&a), want, "{n} workers");
    }
}

/// Builds a raw x86-64 image whose calls pass the edge limit: the entry
/// at 0x401000 calls 64 functions, and each calls the same 64 helpers and
/// one helper of its own, 4,224 calls among 193 functions.
fn wide_calls() -> Program {
    use borer_engine::num::lo32;
    let at = |k: usize| 0x401000 + from_usize(k);
    let mut code = vec![0xccu8; 0x8000];
    let mut calls = |from: usize, to: &[usize]| {
        for (i, &t) in to.iter().enumerate() {
            let site = from + 5 * i;
            code[site] = 0xe8; // ASM: call rel32
            let rel = lo32(at(t).wrapping_sub(at(site + 5)));
            code[site + 1..site + 5].copy_from_slice(&rel.to_le_bytes());
        }
        code[from + 5 * to.len()] = 0xc3; // ASM: ret
    };
    let middle = |i: usize| 0x200 + 0x150 * i;
    let helper = |j: usize| 0x6000 + 0x10 * j;
    let own = |i: usize| 0x7000 + 0x10 * i;
    calls(0, &(0..64).map(middle).collect::<Vec<_>>());
    for i in 0..64 {
        let to: Vec<usize> = (0..64).map(helper).chain([own(i)]).collect();
        calls(middle(i), &to);
        calls(helper(i), &[]);
        calls(own(i), &[]);
    }
    let text = Section::mapped(".text", 0x401000, 0, 0x8000, false, true);
    Program::raw(code, Arch::X86_64, 0x400000, Some(0x401000), vec![text])
}

/// Past the edge limit every node keeps the edge the walk reached it by,
/// the edges left out are counted, and their ends are open.
///
/// The walk spends its budget in rounds of six callees a node and walks on
/// from the callees its second round adds while the depth and the cap
/// leave room, so every function is drawn, its own helper too.
#[test]
fn past_the_edge_limit_every_node_keeps_the_edge_that_reached_it() {
    use borer_engine::analysis::render::{GRAPH_EDGES_MAX, Walk, call_graph};
    let p = wide_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let g = call_graph(&p, &a, &o, 0x401000, Walk::Callees, 3, 1024);
    assert_eq!(g.nodes.len(), 193, "{:?}", g.cut);
    assert!(
        g.nodes
            .iter()
            .any(|n| n.addr == 0x401000 + 0x7000 + 0x10 * 6)
    );
    let cut = g.cut.expect("edges are cut");
    assert_eq!((cut.shown, cut.total, cut.edges_total), (193, 193, 4224));
    assert_eq!(
        (g.edges.len(), cut.edges_shown),
        (GRAPH_EDGES_MAX, GRAPH_EDGES_MAX)
    );
    let reached: std::collections::BTreeSet<usize> = g.edges.iter().map(|e| e.to).collect();
    for k in (0..g.nodes.len()).filter(|&k| k != g.root) {
        assert!(reached.contains(&k), "{:#x} has no edge", g.nodes[k].addr);
    }
    assert!(g.nodes.iter().any(|n| n.open));
    drawn_down(&g, |n| &n.name);
}

/// Builds a raw x86-64 image with one unresolved call.
///
/// `sub_401000` calls `sub_401040`, calls through `rax` and reads the
/// global 0x403000 twice; `sub_401040` calls `sub_401080` twice and takes
/// its address five times.
fn unseen_image() -> Program {
    use borer_engine::num::lo32;
    let mut code = vec![0xccu8; 0x100];
    let rel = |site: usize, len: usize, to: u64| {
        lo32(to.wrapping_sub(0x401000 + from_usize(site + len))).to_le_bytes()
    };
    let mut put = |site: usize, head: &[u8], len: usize, to: u64| {
        code[site..site + head.len()].copy_from_slice(head);
        code[site + head.len()..site + len].copy_from_slice(&rel(site, len, to));
    };
    put(0x00, &[0xe8], 5, 0x401040); // ASM: call sub_401040
    put(0x07, &[0x8b, 0x05], 6, 0x403000); // ASM: mov eax,[rip+0x403000]
    put(0x0d, &[0x8b, 0x05], 6, 0x403000); // ASM: mov eax,[rip+0x403000]
    for k in 0..2 {
        put(0x40 + 5 * k, &[0xe8], 5, 0x401080); // ASM: call sub_401080
    }
    for k in 0..5 {
        put(0x4a + 7 * k, &[0x48, 0x8d, 0x0d], 7, 0x401080); // ASM: lea rcx,[rip+sub_401080]
    }
    code[0x05..0x07].copy_from_slice(&[0xff, 0xd0]); // ASM: call rax
    code[0x13] = 0xc3; // ASM: ret
    code[0x6d] = 0xc3; // ASM: ret
    code[0x80] = 0xc3; // ASM: ret
    code.extend([0u8; 0x10]);
    let sections = vec![
        Section::mapped(".text", 0x401000, 0, 0x100, false, true),
        Section::mapped(".data", 0x403000, 0x100, 0x10, true, false),
    ];
    Program::raw(code, Arch::X86_64, 0x400000, Some(0x401000), sections)
}

/// A reference graph says what it could not see by the rule the xrefs
/// listing follows.
///
/// That is the unresolved calls anywhere while few calls or jumps reach a
/// target that is code or called, and nothing for a global only read.
///
/// The global 0x403000, read by two `mov`s, has no note in the listing
/// and none in the graph. `sub_401080`, with two calls and five data
/// references, has the listing's note in the graph too.
#[test]
fn a_reference_graph_notes_what_it_missed_as_the_listing_does() {
    use borer_engine::analysis::render::{XrefView, xref_graph, xref_rows};
    let p = unseen_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let listed = |target: u64| {
        let text = xref_rows(&p, &a, &o, target, XrefView::Count).spell();
        text.lines()
            .find(|l| l.starts_with("# not seen:"))
            .map(|l| format!("{l}\n"))
    };
    let drawn = |target: u64| xref_graph(&p, &a, &o, target, 1, 16).unseen.line("#");
    assert_eq!(listed(0x403000), None);
    assert_eq!(drawn(0x403000), None);
    let note = listed(0x401080);
    assert!(note.is_some(), "the listing notes the call through rax");
    assert_eq!(drawn(0x401080), note);
}

/// An address no function holds is code when an executable section maps
/// it and data when only a data section does.
#[test]
fn an_address_in_no_function_is_code_only_in_an_executable_section() {
    use borer_engine::analysis::render::{AddrKind, xref_graph};
    let p = unseen_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let kind = |va: u64| {
        xref_graph(&p, &a, &o, va, 1, 4)
            .nodes
            .iter()
            .find(|n| n.addr == va)
            .map(|n| n.kind)
    };
    assert_eq!(kind(0x4010f0), Some(AddrKind::Code));
    assert_eq!(kind(0x403000), Some(AddrKind::Data));
}
