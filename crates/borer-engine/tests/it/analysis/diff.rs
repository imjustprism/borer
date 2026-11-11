//! Clones, fingerprints and the diff between two versions.

use super::*;

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
