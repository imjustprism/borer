//! Function discovery, names, resolution and listings on the fixture.

use super::*;

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
        text.contains("&local_10"),
        "the escaping local is not used: {text}"
    );
    let declared = text.lines().any(|l| {
        l.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .any(|w| w == "local_10")
            && (l.starts_with("uint") || l.starts_with("int") || l.starts_with("char"))
    });
    assert!(
        declared,
        "the escaping local is used but never declared: {text}"
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
    assert_eq!(main.blocks[0].successors[..], [0x1005]);

    let b1 = &main.blocks[1];
    assert_eq!(b1.term.name(), "cond");
    let mut succ: Vec<u64> = b1.successors.to_vec();
    succ.sort_unstable();
    assert_eq!(succ, vec![0x1009, 0x100e]);

    assert_eq!(main.blocks[2].term.name(), "call");
    assert_eq!(main.blocks[2].successors[..], [0x100e]);
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
        names: BTreeMap::new().into(),
        comments: BTreeMap::new().into(),
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

/// A file the loader does not recognize and maps no code from says which
/// `arch` to load it with; a recognized one does not.
///
/// # Panics
///
/// When the hint is missing from the raw file's refusal or added to
/// another's.
#[test]
fn a_raw_file_of_unknown_arch_says_to_name_one() {
    use borer_engine::program::Feature;
    let mut p = Program::raw(vec![0u8; 16], Arch::Unknown, 0, None, Vec::new());
    p.format = BinaryFormat::Raw;
    let why = p.refuses(Feature::Disasm).expect("no code analysis");
    assert!(
        why.ends_with("load it again with arch=x86|x64|arm64 (CLI: --arch)"),
        "{why}"
    );
    p.format = BinaryFormat::Elf;
    let why = p.refuses(Feature::Disasm).expect("no code analysis");
    assert!(!why.contains("arch="), "{why}");
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

/// A function whose own code ends every path at a no-return call ends
/// its callers at their calls to it.
///
/// It calls `exit` through its PLT stub, no name says it never returns,
/// and its caller lays out live code right after the call.
///
/// GCC's `mallocFail.constprop.0` in bzip2recover is this shape, and the
/// caller's walk past the call printed `goto *0x1e60;` after it.
#[test]
fn a_function_whose_body_never_returns_ends_its_callers() {
    let mut bytes = vec![0xccu8; 0x2000];
    let code: &[(usize, &[u8])] = &[
        (0x0, &[0xf3, 0x0f, 0x1e, 0xfa]),                   // ASM: endbr64
        (0x4, &[0xf2, 0xff, 0x25, 0xf5, 0x0f, 0x00, 0x00]), // ASM: bnd jmp [rip+0xff5]
        (0x10, &[0xbf, 0x01, 0x00, 0x00, 0x00]),            // ASM: mov edi,1
        (0x15, &[0xe8, 0xe6, 0xff, 0xff, 0xff]),            // ASM: call 0x1000
        (0x40, &[0x48, 0x85, 0xff]),                        // ASM: test rdi,rdi
        (0x43, &[0x74, 0x01]),                              // ASM: je 0x1046
        (0x45, &[0xc3]),                                    // ASM: ret
        (0x46, &[0xe8, 0xc5, 0xff, 0xff, 0xff]),            // ASM: call 0x1010
        (0x4b, &[0x31, 0xc0]),                              // ASM: xor eax,eax
        (0x4d, &[0xc3]),                                    // ASM: ret
    ];
    for (at, b) in code {
        bytes[*at..*at + b.len()].copy_from_slice(b);
    }
    bytes[0x1000..0x1008].fill(0);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".got", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Elf;
    p.symbols.push(Symbol {
        name: "exit".to_owned(),
        addr: 0x2000,
        kind: SymbolKind::Import,
    });
    let a = Analysis::compute(&p);
    let caller = a.function(0x1040).unwrap();
    assert_eq!(
        caller.end, 0x104b,
        "the caller ran past the call: {caller:?}"
    );
}

/// A row folding the functions that run the same code names them, so each
/// is reachable from the listing: kernelbase's three callers of one helper
/// listed one and counted two that no agent could then find.
#[test]
fn folded_rows_name_the_functions_they_stand_for() {
    use borer_engine::analysis::render::{functions_by_string_tsv, xrefs_tsv};
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let refs = xrefs_tsv(&p, &a, &o, 0x2040, 0, 60, false);
    let by_string = functions_by_string_tsv(&p, &a, &o, "BORER", 0, 10);
    assert!(
        refs.contains(
            "sub_4d80: 0x4d80 imm/mem (+1 function running the same code): sub_4d90
"
        ),
        "{refs}"
    );
    assert!(
        by_string.contains(
            "0x4d80 sub_4d80: 1 (+1 function running the same code): sub_4d90
"
        ),
        "{by_string}"
    );
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

/// A linear sweep stops where the containing function's code stops.
///
/// `T` is a two-instruction import thunk; the bytes after it belong to the
/// next function, not to this one, so a sweep that starts at `T` must not
/// run on into them.
#[test]
fn a_sweep_stops_at_the_end_of_its_function() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let f = a.function(0x1210).expect("T is a function");
    assert_eq!(
        borer_engine::analysis::render::sweep_limit(&p, &a, 0x1210),
        Some(f.end)
    );
    assert_eq!(
        borer_engine::analysis::render::sweep_limit(&p, &a, 0x2040),
        None
    );
}

/// A sweep crosses the alignment padding before a loop head and runs on to
/// the end of the function's code.
///
/// sqlite3 aligns a loop with `nop word [rax+rax]` after a `jmp`, and
/// `disassemble` said the code ended there and data followed, eight
/// hundred bytes short of the function's end.
///
/// # Panics
///
/// When the sweep stops at the padding.
#[test]
fn a_sweep_crosses_alignment_padding() {
    // ASM: jmp 0x1010; nop word [rax+rax] (6 bytes); then at 0x1010:
    // ASM: inc rdx; cmp rdx,8; jb 0x1010; ret
    let code: &[u8] = &[
        0xeb, 0x0e, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00, 0x66,
        0x90, 0x48, 0xff, 0xc2, 0x48, 0x83, 0xfa, 0x08, 0x72, 0xf7, 0xc3,
    ];
    let mut bytes = vec![0xccu8; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
    );
    p.function_ranges = vec![(0x1000, 0x1000 + from_usize(code.len()))];
    let a = Analysis::compute(&p);
    let end = a.function(0x1000).expect("a function at 0x1000").end;
    assert_eq!(
        borer_engine::analysis::render::sweep_limit(&p, &a, 0x1000),
        Some(end)
    );
    assert!(end > 0x1010, "{end:#x}");
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
