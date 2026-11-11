//! Functions, references, call graphs and listings of 32-bit images.

use super::*;

/// The value passes speak the registers a 32-bit program has: `taint`
/// follows `eax` by default and accepts `ecx`, and `layout` reads through
/// `ecx` by default, on `mov eax,[ecx+4]; mov ebx,eax; ret`.
#[test]
fn taint_and_layout_speak_32_bit_registers() {
    use borer_engine::analysis::render::{layout_tsv, taint_tsv};
    let p = image(&[0x8b, 0x41, 0x04, 0x8b, 0xd8, 0xc3]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let taint = taint_tsv(&p, &a, &o, "0x401000").unwrap();
    assert!(taint.starts_with("# eax from"), "{taint}");
    let explicit = taint_tsv(&p, &a, &o, "0x401000,ecx").unwrap();
    assert!(!explicit.contains("not a general register"), "{explicit}");
    let refused = taint_tsv(&p, &a, &o, "0x401000,r8").unwrap_err();
    assert!(refused.contains("use eax..edi"), "{refused}");
    let layout = layout_tsv(&p, &a, &o, "0x401000").unwrap();
    assert!(layout.contains("through ecx"), "{layout}");
    assert!(layout.contains("0x4 "), "{layout}");
}

/// A function a data pointer names is found even when another function's
/// span reaches over it.
///
/// The entry `jmp 0x401100` tail-jumps into a block far below, so its span
/// runs from 0x401000 to 0x401101 and covers 0x401040; the function there,
/// `mov eax,1; ret`, is named only by a pointer in `.rdata`. Its bytes lie
/// in no block of the entry, and a pointer into unclaimed code is a
/// function.
#[test]
fn a_pointer_into_another_functions_span_still_seeds_a_function() {
    let mut code = vec![0xe9, 0xfb, 0x00, 0x00, 0x00];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x100, 0xcc);
    code.push(0xc3);
    let p = image_with_data(&code, &[0x40, 0x10, 0x40, 0x00]);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401040).is_some(),
        "the pointed-to function is missing"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401040).unwrap_or_default();
    assert!(text.contains("return 1;"), "{text}");
}

/// A table read through a scaled index, `mov eax,[ecx*4+0x402000]; ret`,
/// is a reference to the table, of the `index` kind: `xrefs` on the table
/// finds the instruction.
#[test]
fn an_indexed_table_read_is_a_reference_to_the_table() {
    use borer_engine::analysis::render::xrefs_tsv;
    let p = image_with_data(
        &[0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0xc3],
        &[0u8; 16],
    );
    let a = Analysis::compute(&p);
    let refs = xrefs_tsv(&p, &a, &Overlay::default(), 0x402000, 0, 60, false);
    assert!(refs.contains("# 1 xrefs to 0x402000"), "{refs}");
    assert!(refs.contains("sub_401000: 0x401000 index\n"), "{refs}");
}

/// A conditional tail call, `jne` into another function, is a reference to
/// that function, like the `call` beside it.
///
/// `call 0x401010; test ecx,ecx; jne 0x401010; ret`, padding, then
/// `xor eax,eax; ret` at 0x401010: only the call was listed.
#[test]
fn a_conditional_tail_call_is_a_reference() {
    use borer_engine::analysis::render::xrefs_tsv;
    let mut code = vec![0xe8, 0x0b, 0x00, 0x00, 0x00, 0x85, 0xc9, 0x75, 0x07, 0xc3];
    code.extend_from_slice(&[0xcc; 6]);
    let p = image(&[code, vec![0x31, 0xc0, 0xc3]].concat());
    let a = Analysis::compute(&p);
    assert!(a.function(0x401010).is_some(), "the callee is missing");
    let refs = xrefs_tsv(&p, &a, &Overlay::default(), 0x401010, 0, 60, false);
    assert!(
        refs.contains("0x401000 call, 0x401007 jmp"),
        "the conditional tail call is missing: {refs}"
    );
}

/// An operand naming the mapped headers is a reference to them: `mov eax,
/// 0x400000` names the image base, which no section maps.
#[test]
fn an_operand_naming_the_headers_is_a_reference() {
    use borer_engine::analysis::render::xrefs_tsv;
    let mut bytes = vec![0u8; 0x400];
    bytes.extend_from_slice(&[0xb8, 0x00, 0x00, 0x40, 0x00, 0xc3]);
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0x400000,
        Some(0x401000),
        vec![Section::mapped(".text", 0x401000, 0x400, 6, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let refs = xrefs_tsv(&p, &a, &Overlay::default(), 0x400000, 0, 60, false);
    assert!(
        refs.contains("sub_401000: 0x401000 imm/mem"),
        "the header reference is missing: {refs}"
    );
}

/// A reference into the middle of a wide string reads the whole string, as
/// one into an ASCII string does, and the filter matches a string's text,
/// not the quotes it is printed in.
#[test]
fn a_string_search_reads_wide_strings_whole_and_ignores_quotes() {
    use borer_engine::analysis::render::functions_by_string_tsv;
    let p = strings_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let wide = functions_by_string_tsv(&p, &a, &o, "widestring", 0, 50);
    assert!(wide.contains("L\"widestring\""), "{wide}");
    assert!(wide.contains("sub_401020: 1"), "{wide}");
    let quote = functions_by_string_tsv(&p, &a, &o, "\"", 0, 50);
    assert!(quote.contains(": 0 function/string pairs"), "{quote}");
    let broken = functions_by_string_tsv(&p, &a, &o, "x\ny", 0, 50);
    let head = broken.lines().next().unwrap_or_default();
    assert!(
        head.contains("match 'x") && head.contains("across"),
        "the echoed filter broke the header line: {broken}"
    );
}

/// A string search pages its rows and numbers at most `limit` strings,
/// the first row included, counting what it leaves out.
#[test]
fn a_string_search_pages_and_keeps_its_legend_within_the_limit() {
    use borer_engine::analysis::render::functions_by_string_tsv;
    let p = strings_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let one = functions_by_string_tsv(&p, &a, &o, "a", 0, 1);
    assert!(
        one.starts_with("# showing 1 of 1 row: 2 function/string pairs"),
        "{one}"
    );
    assert!(one.contains("# strings: 1=\"alpha one\"\n"), "{one}");
    assert!(one.contains("sub_401000: 1 (+1 more strings)"), "{one}");
    let all = functions_by_string_tsv(&p, &a, &o, "", 0, 1);
    assert!(all.starts_with("# showing 1 of 2 rows"), "{all}");
    assert!(
        all.contains("# 1 more rows; offset=1 for the next page"),
        "{all}"
    );
    let second = functions_by_string_tsv(&p, &a, &o, "", 1, 50);
    assert!(second.starts_with("# showing 1 of 2 rows"), "{second}");
    assert!(second.contains("sub_401020: 1\n"), "{second}");
    assert!(!second.contains("sub_401000"), "{second}");
}

/// Walking the callers of an import labels the root by the import, drawn
/// as the stadium an import is, where it read `sub_<slot>`; the count line
/// is a mermaid comment.
#[test]
fn a_callgraph_over_an_import_names_its_root() {
    use borer_engine::analysis::render::callgraph_mermaid;
    let p = import_call_image();
    let a = Analysis::compute(&p);
    let out = callgraph_mermaid(&p, &a, &Overlay::default(), 0x402000, 30, true);
    assert!(out.contains("  n0([\"GetTickCount\"])\n"), "{out}");
    assert!(!out.contains("sub_402000"), "{out}");
    assert!(out.lines().all(|l| !l.starts_with('#')), "{out}");
    assert!(
        out.lines().last().unwrap_or_default().starts_with("%% "),
        "{out}"
    );
}

/// A control-flow graph pages its blocks by offset and says which it drew
/// on a mermaid comment line.
///
/// `test ecx,ecx; je +1; nop; ret` is three blocks; from the second, two
/// are drawn.
#[test]
fn a_cfg_pages_its_blocks_on_a_mermaid_comment() {
    use borer_engine::analysis::render::cfg_mermaid;
    let p = image(&[0x85, 0xc9, 0x74, 0x01, 0x90, 0xc3]);
    let a = Analysis::compute(&p);
    let out = cfg_mermaid(&a, &Overlay::default(), 0x401000, 1).unwrap_or_default();
    assert!(out.contains("%% showing 2 of 3 blocks from 1\n"), "{out}");
    assert!(out.contains("[\"0x401004 "), "{out}");
    assert!(!out.contains("[\"0x401000 "), "{out}");
    assert!(out.lines().all(|l| !l.starts_with('#')), "{out}");
}

/// A pointer in data to data a linker merged into `.text` is a reference,
/// as one to data in a data section is: the word at 0x402000 names zero
/// bytes at 0x401100 that no block covers.
#[test]
fn a_pointer_to_data_in_an_executable_section_is_a_reference() {
    use borer_engine::analysis::render::xrefs_tsv;
    let p = image_with_data(&[0xc3], &[0x00, 0x11, 0x40, 0x00]);
    let a = Analysis::compute(&p);
    assert!(a.function_at(0x401100).is_none(), "the data became code");
    let refs = xrefs_tsv(&p, &a, &Overlay::default(), 0x401100, 0, 60, false);
    assert!(
        refs.contains("-: 0x402000 ptr"),
        "the pointer is missing: {refs}"
    );
}

/// Two reads of one table from one function are two sites on the
/// function's row, not one site folded with "1 more running the same code":
/// `mov eax,[ecx*4+0x402000]; add eax,[edx*4+0x402000]; ret`.
#[test]
fn two_reads_from_one_function_are_two_reference_rows() {
    use borer_engine::analysis::render::xrefs_tsv;
    let p = image_with_data(
        &[
            0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0x03, 0x04, 0x95, 0x00, 0x20, 0x40, 0x00,
            0xc3,
        ],
        &[0u8; 16],
    );
    let a = Analysis::compute(&p);
    let refs = xrefs_tsv(&p, &a, &Overlay::default(), 0x402000, 0, 60, false);
    assert!(
        refs.contains("sub_401000: 0x401000 index, 0x401007 index\n"),
        "{refs}"
    );
    assert!(!refs.contains("running the same code"), "{refs}");
}

/// A function whose only reference is an immediate stored into an object,
/// `mov dword [esi+0x2c],0x401040; ret`, a callback slot being filled, is
/// discovered from that immediate.
#[test]
fn a_callback_stored_by_immediate_is_a_function() {
    let mut code = vec![0xc7, 0x46, 0x2c, 0x40, 0x10, 0x40, 0x00, 0xc3];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401040).is_some(),
        "the stored callback is missing"
    );
}

/// A callback stored by a function that padding found late is still discovered.
///
/// `ret` at the entry, `int3` padding, then at 0x401010
/// `mov dword [esi+0x2c],0x401040; ret` naming `mov eax,1; ret` at
/// 0x401040, which nothing else mentions.
#[test]
fn a_callback_stored_by_a_late_function_is_still_seeded() {
    let mut code = vec![0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xc7, 0x46, 0x2c, 0x40, 0x10, 0x40, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401010).is_some(),
        "the padding-seeded function is missing"
    );
    assert!(
        a.function(0x401040).is_some(),
        "the stored callback is missing"
    );
}

/// `read` walks the strings of a pool: `"ab\0\0cd\0"` read as three
/// C strings gives `"ab"` and `"cd"`, stepping over the padding between
/// them, and stops when the pool ends.
#[test]
fn reading_several_strings_walks_the_pool() {
    use borer_engine::memory::{Kind, read_values};
    let p = image_with_data(&[0xc3], b"ab\0\0cd\0");
    let v = read_values(&p, 0x402000, Kind::CStr, 3).expect("strings read");
    let texts: Vec<&str> = v.iter().map(|x| x.text.as_str()).collect();
    assert_eq!(texts, ["\"ab\" (len 2)", "\"cd\" (len 2)"]);
    assert_eq!(v[1].at, 0x402004);
}

/// An address inside an instruction resolves to the instruction's start:
/// byte 3 of `mov eax,[ecx*4+0x402000]` (seven bytes) is 0x401000, and the
/// `ret` after it is its own boundary.
#[test]
fn an_address_inside_an_instruction_snaps_to_its_start() {
    use borer_engine::analysis::render::instruction_at_or_before;
    let p = image(&[0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0xc3]);
    let a = Analysis::compute(&p);
    assert_eq!(instruction_at_or_before(&p, &a, 0x401003), Some(0x401000));
    assert_eq!(instruction_at_or_before(&p, &a, 0x401007), Some(0x401007));
    assert_eq!(instruction_at_or_before(&p, &a, 0x401100), None);
}

/// A word in data that lands in data is a `ptr` reference from its slot,
/// a word that lands on a function is a `table` one, and a small constant
/// is neither.
///
/// The words at 0x402000: 0x402010 (into `.rdata`), 0x401000 (the
/// function), and 5.
#[test]
fn a_pointer_stored_in_data_is_a_reference_to_what_it_points_at() {
    let mut data = vec![0u8; 0x20];
    data[..4].copy_from_slice(&0x402010u32.to_le_bytes());
    data[4..8].copy_from_slice(&0x401000u32.to_le_bytes());
    data[8..12].copy_from_slice(&5u32.to_le_bytes());
    let p = image_with_data(&[0xc3], &data);
    let a = Analysis::compute(&p);
    let ptr: Vec<(u64, RefKind, Option<u64>)> = a
        .xrefs_to(0x402010)
        .iter()
        .map(|s| (s.va, s.kind, s.from_entry))
        .collect();
    assert_eq!(ptr, [(0x402000, RefKind::Ptr, None)]);
    assert!(
        a.xrefs_to(0x401000)
            .iter()
            .any(|s| s.va == 0x402004 && s.kind == RefKind::Table),
        "{:?}",
        a.xrefs_to(0x401000)
    );
    assert!(a.xrefs_to(5).is_empty());
}

/// A near call to an address outside executable memory seeds no function.
///
/// `call 0x10000; ret` at the entry calls below the image base, where nothing
/// is mapped. An obfuscated operand or a byte of decrypted data read as code
/// can encode a call to anywhere, and following it once seeded a phantom empty
/// function that nothing could walk. Discovery keeps only the entry.
#[test]
fn a_call_outside_executable_memory_seeds_no_function() {
    let p = image(&[0xe8, 0xfb, 0xef, 0xc0, 0xff, 0xc3]);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x0001_0000).is_none(),
        "a call below the image base seeded a phantom function"
    );
    assert!(a.function(0x0040_1000).is_some(), "the entry was lost");
    let outside: Vec<u64> = a
        .functions
        .iter()
        .map(|f| f.entry)
        .filter(|e| {
            !p.sections
                .iter()
                .any(|s| *e >= s.va.0 && *e < s.va.0 + s.vsize)
        })
        .collect();
    assert!(
        outside.is_empty(),
        "functions seeded outside every section: {outside:#x?}"
    );
}

/// A seed that decodes to nothing produces no empty function.
///
/// A data pointer into `.text` points at `ff ff`, which does not decode. The
/// pointer scan seeds it, the walk finds no instruction, and the result is not
/// a function: discovery drops it rather than list a zero-instruction body,
/// the noise a decrypted image otherwise fills with.
#[test]
fn a_seed_that_decodes_to_nothing_is_not_a_function() {
    let mut code = vec![0xc3u8; 0x20];
    code[0x10] = 0xff;
    code[0x11] = 0xff;
    let data = 0x0040_1010u32.to_le_bytes();
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x0040_1010).is_none(),
        "an undecodable seed became a function"
    );
    let empty: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.instr_count == 0)
        .map(|f| f.entry)
        .collect();
    assert!(
        empty.is_empty(),
        "zero-instruction functions listed: {empty:#x?}"
    );
}

/// A listing that starts in read-only data says so, one that starts in
/// `.text` outside every function says that, and one inside a function
/// says nothing.
#[test]
fn a_listing_outside_code_carries_a_caveat() {
    use borer_engine::analysis::render::listing_caveat;
    let p = image_with_data(&[0xc3], &[0x0f, 0xa2, 0xc3]);
    let a = Analysis::compute(&p);
    let data = listing_caveat(&p, &a, 0x402000);
    assert!(data.contains(".rdata (r--)"), "{data}");
    assert!(data.contains("never executes"), "{data}");
    let gap = listing_caveat(&p, &a, 0x401800);
    assert!(gap.contains("outside every discovered function"), "{gap}");
    assert_eq!(listing_caveat(&p, &a, 0x401000), "");
}

/// An import a function calls through its slot is a leaf of its callgraph,
/// named after the import without its DLL and drawn as a stadium; a near
/// callee is a box.
///
/// 0x401000: `call [0x402100]; call 0x401010; ret`, with `QString::QString`
/// behind the slot and `mov eax,1; ret` at 0x401010.
#[test]
fn an_import_is_a_leaf_of_the_callgraph() {
    use borer_engine::analysis::render::callgraph_mermaid;
    let mut code = vec![
        0xff, 0x15, 0x00, 0x21, 0x40, 0x00, 0xe8, 0x05, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut p = image_with_data(&code, &[0u8; 0x110]);
    p.symbols = vec![Symbol {
        name: "Qt5Core.dll!??0QString@@QAE@XZ".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let out = callgraph_mermaid(&p, &a, &Overlay::default(), 0x401000, 30, false);
    assert!(out.contains("([\"QString::QString\"])"), "{out}");
    assert!(out.contains("[\"sub_401010\"]"), "{out}");
    assert!(out.contains("%% 3 nodes, 1 imports"), "{out}");
    assert_eq!(out.matches(" --> ").count(), 2, "{out}");
    let mut o = Overlay::default();
    o.names
        .insert(0x401010, "Core::Ptr<UI::Canvas>::operator ->".to_owned());
    let out = callgraph_mermaid(&p, &a, &o, 0x401000, 30, false);
    assert!(
        out.contains("[\"Core::Ptr#lt;UI::Canvas#gt;::operator -#gt;\"]"),
        "{out}"
    );
}

/// An import thunk is marked with the slot it jumps through, left out of
/// the function listing with a note, and listed alone under `thunk`.
///
/// 0x401000: `call 0x401010; ret`; 0x401010: `jmp [0x402100]` through
/// `QString::QString`.
#[test]
fn an_import_thunk_is_listed_apart_from_the_functions() {
    use borer_engine::analysis::render::{FunctionOrder, function_detail, functions_tsv};
    let mut code = vec![0xe8, 0x0b, 0x00, 0x00, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xff, 0x25, 0x00, 0x21, 0x40, 0x00]);
    let mut p = image_with_data(&code, &[0u8; 0x110]);
    p.symbols = vec![Symbol {
        name: "Qt5Core.dll!??0QString@@QAE@XZ".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(a.function(0x401010).and_then(|f| f.thunk), Some(0x402100));
    let (_, total, all) = functions_tsv(&a, &o, None, FunctionOrder::Address, 0, 50);
    assert_eq!(total, 1, "{all}");
    assert!(all.contains("1 import thunks left out"), "{all}");
    assert!(!all.contains("0x401010"), "{all}");
    let (_, only, page) = functions_tsv(&a, &o, Some("thunk"), FunctionOrder::Address, 0, 50);
    assert_eq!(only, 1, "{page}");
    assert!(page.contains("0x401010"), "{page}");
    let detail = function_detail(&a, &o, 0x401010, 0).unwrap_or_default();
    assert!(detail.contains("thunk:   jmp [0x402100]"), "{detail}");
}

/// On a program with no protection signal the reading list still names
/// the function that references the most strings and imports, and says
/// that is the ranking.
///
/// 0x401000 pushes three string addresses and calls `GetTickCount`
/// through its slot.
#[test]
fn triage_ranks_by_strings_and_imports_when_nothing_else_stands_out() {
    use borer_engine::analysis::render::triage_tsv;
    let code = [
        0x68, 0x00, 0x20, 0x40, 0x00, 0x68, 0x08, 0x20, 0x40, 0x00, 0x68, 0x10, 0x20, 0x40, 0x00,
        0xff, 0x15, 0x00, 0x21, 0x40, 0x00, 0x83, 0xc4, 0x0c, 0xc3,
    ];
    let mut data = vec![0u8; 0x110];
    data[..6].copy_from_slice(b"alpha\0");
    data[8..14].copy_from_slice(b"bravo\0");
    data[0x10..0x18].copy_from_slice(b"charlie\0");
    let mut p = image_with_data(&code, &data);
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetTickCount".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let text = triage_tsv(&p, &a, &Overlay::default());
    assert!(text.contains("no protection signal fired"), "{text}");
    assert!(
        text.contains("references 3 strings and 1 imports"),
        "{text}"
    );
}

/// A typed read that finds nothing says which of two things went wrong:
/// the address maps to no bytes, or the bytes are not the kind asked for.
#[test]
fn a_failed_read_says_whether_the_address_is_mapped() {
    use borer_engine::memory::{Kind, read_values};
    let p = image_with_data(&[0xc3], &[0xa2, 0x2b, 0x04, 0x00]);
    let unmapped = read_values(&p, 0x900000, Kind::CStr, 1)
        .err()
        .unwrap_or_default();
    assert!(unmapped.contains("not mapped"), "{unmapped}");
    let wrong = read_values(&p, 0x402000, Kind::CStr, 1)
        .err()
        .unwrap_or_default();
    assert!(wrong.contains("no CStr at 0x402000"), "{wrong}");
    assert!(wrong.contains("0xa2"), "{wrong}");
}

/// A read through `fs` is a field of the thread environment block:
/// `mov eax,fs:[0x18]` is the TEB's own address, `fs:[0x30]` the PEB.
#[test]
fn a_read_through_fs_names_the_teb_field() {
    let text = dc(&[0x64, 0xa1, 0x18, 0x00, 0x00, 0x00, 0xc3]);
    assert!(
        text.contains("return NtCurrentTeb()->NtTib.Self;"),
        "{text}"
    );
    let text = dc(&[0x64, 0xa1, 0x30, 0x00, 0x00, 0x00, 0xc3]);
    assert!(
        text.contains("NtCurrentTeb()->ProcessEnvironmentBlock"),
        "{text}"
    );
}

/// A word in the resource section that spells a code address seeds no
/// function, while the same word in `.rdata` does.
///
/// Three functions back to back with no padding between them, `ret` at
/// 0x401000 and `mov eax,N; ret` at 0x401001 and 0x401007: `.rdata`
/// holds 0x401007 and `.rsrc` holds 0x401001, and only the first becomes
/// a function.
#[test]
fn a_resource_word_seeds_no_function() {
    let code = [
        0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x3000];
    bytes[..code.len()].copy_from_slice(&code);
    bytes[0x1000..0x1004].copy_from_slice(&0x401007u32.to_le_bytes());
    bytes[0x2000..0x2004].copy_from_slice(&0x401001u32.to_le_bytes());
    let p = Program::raw(
        bytes,
        Arch::X86,
        0x400000,
        Some(0x401000),
        vec![
            Section::mapped(".text", 0x401000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x402000, 0x1000, 0x1000, false, false),
            Section::mapped(".rsrc", 0x403000, 0x2000, 0x1000, false, false),
        ],
    );
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert!(entries.contains(&0x401007), "{entries:x?}");
    assert!(!entries.contains(&0x401001), "{entries:x?}");
}

/// A jump table in `.text` is referenced as a table, and its base is no
/// function.
///
/// `mov eax,[esp+4]; cmp eax,1; ja 0x401010; jmp [eax*4+0x401011]; ret`
/// with the table right after the `ret`, naming the two `ret`s that
/// follow it; nothing is padded, so no gap walk reaches the table.
#[test]
fn a_jump_tables_base_is_no_function() {
    let mut code = vec![
        0x8b, 0x44, 0x24, 0x04, 0x83, 0xf8, 0x01, 0x77, 0x07, 0xff, 0x24, 0x85, 0x11, 0x10, 0x40,
        0x00, 0xc3,
    ];
    code.extend_from_slice(&0x401019u32.to_le_bytes());
    code.extend_from_slice(&0x40101au32.to_le_bytes());
    code.extend_from_slice(&[0xc3, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert!(!entries.contains(&0x401011), "{entries:x?}");
    assert_eq!(
        a.xrefs_to(0x401011).first().map(|s| s.kind),
        Some(RefKind::Index)
    );
}

/// A callee that sets `ecx` with `or ecx, -1` reads no argument in it, so
/// its caller passes none.
///
/// The caller `mov ecx,5; call 0x401020; ret` calls `or ecx,-1; mov
/// eax,ecx; ret`.
#[test]
fn an_or_with_minus_one_sets_the_register_without_reading_it() {
    let mut code = vec![
        0xb9, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x83, 0xc9, 0xff, 0x8b, 0xc1, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("sub_401020()"), "{text}");
    let callee = decompile(&p, &a, &Overlay::default(), 0x401020).unwrap_or_default();
    assert!(callee.contains("sub_401020()"), "{callee}");
    assert!(
        callee.contains("return -1;") || callee.contains("return 0xffffffff;"),
        "{callee}"
    );
}

/// A countdown `sub ebx, 1; jne` reads the counter it just wrote, not a
/// copy of what it held.
///
/// `mov ebx,2; L: call 0x401020; sub ebx,1; jne L; ret`, the callee `mov
/// eax,1; ret`.
#[test]
fn a_countdown_reads_the_counter_it_just_wrote() {
    let mut code = vec![
        0xbb, 0x02, 0x00, 0x00, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0x83, 0xeb, 0x01, 0x75, 0xf6,
        0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("while (var1 != 0)"), "{text}");
    assert!(!text.contains("tmp_"), "{text}");
}

/// A 32-bit constant with its sign bit set and a small magnitude is the
/// negative number the source wrote.
///
/// `mov eax,-1; ret` returns `-1`, and `add eax,-4` is `a1 - 4`, where a
/// flag like `0x80000000` stays hex.
#[test]
fn small_negative_constants_read_as_negative_on_32_bits() {
    let text = dc(&[0xb8, 0xff, 0xff, 0xff, 0xff, 0xc3]);
    assert!(text.contains("return -1;"), "{text}");
    let text = dc(&[0x8b, 0x44, 0x24, 0x04, 0x83, 0xc0, 0xfc, 0xc3]);
    assert!(text.contains("return a1 - 4;"), "{text}");
    let text = dc(&[0xb8, 0x00, 0x00, 0x00, 0x80, 0xc3]);
    assert!(text.contains("return 0x80000000;"), "{text}");
}

/// A constant multiplied, added or compared is a number even where its
/// value is the address of a string in the image; only a load through it
/// reads the string.
///
/// "abcde" at 0x402000, `a1 = [esp+4]`: `imul eax,[esp+4],0x402000; ret`,
/// `mov eax,[esp+4]; add eax,0x402002; ret` (inside the string), `mov
/// eax,[esp+4]; cmp eax,0x402000; jl L; mov eax,1; ret; L: xor eax,eax;
/// ret` and `mov eax,[esp+4]; movzx eax,byte [eax+0x402000]; ret`.
#[test]
fn only_a_load_reads_a_constant_as_the_string_at_its_value() {
    let data = b"abcde\0";
    let mul = dc_data(
        &[0x69, 0x44, 0x24, 0x04, 0x00, 0x20, 0x40, 0x00, 0xc3],
        data,
        &[],
    );
    assert!(mul.contains("0x402000"), "{mul}");
    assert!(!mul.contains('"'), "{mul}");
    let add = dc_data(
        &[0x8b, 0x44, 0x24, 0x04, 0x05, 0x02, 0x20, 0x40, 0x00, 0xc3],
        data,
        &[],
    );
    assert!(add.contains("0x402002"), "{add}");
    assert!(!add.contains('"'), "{add}");
    let cmp = dc_data(
        &[
            0x8b, 0x44, 0x24, 0x04, 0x3d, 0x00, 0x20, 0x40, 0x00, 0x7c, 0x06, 0xb8, 0x01, 0x00,
            0x00, 0x00, 0xc3, 0x33, 0xc0, 0xc3,
        ],
        data,
        &[],
    );
    assert!(cmp.contains("0x402000"), "{cmp}");
    assert!(!cmp.contains('"'), "{cmp}");
    let load = dc_data(
        &[
            0x8b, 0x44, 0x24, 0x04, 0x0f, 0xb6, 0x80, 0x00, 0x20, 0x40, 0x00, 0xc3,
        ],
        data,
        &[],
    );
    assert!(load.contains("\"abcde\""), "{load}");
}

/// Position-independent code reading its own address stays one function.
///
/// `call $+5; pop ebx` goes to the next instruction, so it is no call, and
/// the rest of the function is no second function. gcc and clang open
/// every i386 PIC function that reaches a global this way;
/// `hard_O2.x86.so` listed 110 functions for 85, each split in two.
#[test]
fn reading_the_program_counter_is_not_a_call() {
    // ASM: push ebx; call $+5; pop ebx; add ebx,0x1000; mov eax,1; pop ebx; ret
    let code = [
        0x53, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x81, 0xc3, 0x00, 0x10, 0x00, 0x00, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0x5b, 0xc3,
    ];
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(a.function(0x401006).is_none_or(|f| f.entry == 0x401000));
    let f = a.function(0x401000).expect("the function");
    assert!(f.callees.is_empty(), "{:x?}", f.callees);
    assert_eq!(a.functions.len(), 1);
}

/// An i386 PLT entry, `jmp [ebx+N]` through the global offset table that
/// `ebx` holds, is named for the import whose slot it reads.
///
/// The slot is `.got.plt` plus N; without that sum no PLT entry of a
/// 32-bit shared object had a name, `xrefs(strlen)` found no call, and
/// `symbols` called the import unreferenced.
#[test]
fn an_i386_plt_entry_is_named_for_its_import() {
    let mut bytes = vec![0u8; 0x3000];
    // ASM: jmp [ebx+0xc]
    bytes[0x1000..0x1006].copy_from_slice(&[0xff, 0xa3, 0x0c, 0x00, 0x00, 0x00]);
    // ASM: call 0x1000; ret
    bytes[0x1008..0x100e].copy_from_slice(&[0xe8, 0xf3, 0xff, 0xff, 0xff, 0xc3]);
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        None,
        vec![
            Section::mapped(".plt", 0x1000, 0x1000, 0x10, false, true),
            Section::mapped(".got.plt", 0x2000, 0x2000, 0x20, true, false),
        ],
    );
    p.format = BinaryFormat::Elf;
    p.function_ranges = vec![(0x1000, 0x1006), (0x1008, 0x100e)];
    p.symbols.push(Symbol {
        name: "strlen".to_owned(),
        addr: 0x200c,
        kind: SymbolKind::Import,
    });
    let a = Analysis::compute(&p);
    let f = a.function(0x1000).expect("the PLT entry");
    assert_eq!(f.name.as_deref(), Some("strlen"));
    assert_eq!(f.thunk, Some(0x200c));
    let (_, _, listed) = borer_engine::analysis::render::symbols_tsv(&p, &a, None, None, 0, 10);
    assert!(!listed.contains("unreferenced"), "{listed}");
}

/// A PE export whose bytes are an integer is not seeded as a function.
///
/// msvcrt exports `_sys_nerr` from `.text`; walked as code it made a
/// 7,500-byte function of the error-string table. The export beside it
/// that is code stays a function.
#[test]
fn a_pe_export_holding_an_integer_is_no_function() {
    // ASM: mov eax,1; ret
    let mut code = vec![0x2bu8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x1000, 0xcc);
    let mut p = Program::raw(
        code,
        Arch::X86,
        0x400000,
        None,
        vec![Section::mapped(".text", 0x401000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    for (name, addr) in [("_sys_nerr", 0x401000), ("one", 0x401010)] {
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Export,
        });
    }
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401000).is_none(),
        "{:x?}",
        a.function(0x401000).map(|f| f.entry)
    );
    assert_eq!(a.function(0x401010).map(|f| f.entry), Some(0x401010));
}
