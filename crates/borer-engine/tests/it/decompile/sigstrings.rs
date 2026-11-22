//! Which string an assert hands its reporter names the function: the
//! signature in the function-name position, never the condition text.
//!
//! GitHub issue 28: `audio::GetDefaultSourceArray(audio::SourceType)` asserts
//! `thread_util::IsMainThread()` and `false && "Unsupported SourceType"`,
//! each call passing Clang's `__PRETTY_FUNCTION__` last. borer took the first
//! condition for the function's own signature, named it
//! `thread_util::IsMainThread`, gave it a `this`, printed the condition as
//! `__FUNCSIG__`, warned that `__FUNCSIG__` was undeclared and listed only
//! the second assert.
//!
//! A call-shaped string (`Class::Method()`) is often a trace of the
//! method's own name, so it may still name a function, unsure, when no
//! other function references it and no full signature or second such
//! string competes.

use borer_engine::analysis::decompile::{answer_header, decompile};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::{from_usize, lo32};
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

/// The source file both asserts cite, at offset 0x100 of the data page.
const PATH: &str = "audio/SourceArray.cpp";

/// The first assert's condition, at offset 0x140: a call expression.
const COND1: &str = "thread_util::IsMainThread()";

/// The second assert's condition, at offset 0x180.
const COND2: &str = "false && \"Unsupported SourceType\"";

/// The pretty-function string both asserts pass last, at offset 0x200.
const PRETTY: &str = "audio::SourceArray &audio::GetDefaultSourceArray(audio::SourceType)";

/// Returns a read-only page holding the strings at their offsets, the
/// last one `last` in place of [`PRETTY`].
///
/// # Arguments
///
/// * `last` - The text each assert passes in the function-name position.
fn strings(last: &str) -> Vec<u8> {
    let mut page = vec![0u8; 0x1000];
    for (off, text) in [(0x100, PATH), (0x140, COND1), (0x180, COND2), (0x200, last)] {
        page[off..off + text.len()].copy_from_slice(text.as_bytes());
    }
    page
}

/// Returns an x64 instruction at `at` whose last four bytes reach `to`.
///
/// # Arguments
///
/// * `at` - Where the instruction starts.
/// * `op` - Its bytes before the displacement.
/// * `to` - The address it reaches.
fn rip(at: u64, op: &[u8], to: u64) -> Vec<u8> {
    let end = at + from_usize(op.len()) + 4;
    [op, &lo32(to.wrapping_sub(end)).to_le_bytes()].concat()
}

/// Returns an x64 image of the reported function at 0x1000, its callee at
/// 0x1100 reading a writable word, and the reporter as an import.
///
/// `push rbx; mov ebx, ecx; call IsMainThread; test eax, eax; jnz A;
/// assert(COND1, PATH, 54, last); A: cmp ebx, 3; je R; test ebx, ebx; jz R;
/// assert(COND2, PATH, 61, last); R: pop rbx; ret`.
///
/// # Arguments
///
/// * `last` - The text each assert passes in the function-name position.
fn x64(last: &str) -> Program {
    let data = 0x2000u64;
    let report = |at: u64, cond: u64, line: u32| {
        let mut c = rip(at, &[0x48, 0x8d, 0x0d], data + cond); // ASM: lea rcx, [cond]
        c.extend(rip(at + 7, &[0x48, 0x8d, 0x15], data + 0x100)); // ASM: lea rdx, [path]
        c.extend([&[0x41, 0xb8][..], &line.to_le_bytes()].concat()); // ASM: mov r8d, line
        c.extend(rip(at + 20, &[0x4c, 0x8d, 0x0d], data + 0x200)); // ASM: lea r9, [last]
        c.extend(rip(at + 27, &[0xff, 0x15], data)); // ASM: call [reporter]
        c
    };
    let mut code = vec![0x53, 0x89, 0xcb]; // ASM: push rbx; mov ebx, ecx
    code.extend(rip(0x1003, &[0xe8], 0x1100)); // ASM: call IsMainThread
    code.extend([0x85, 0xc0, 0x75, 0x21]); // ASM: test eax, eax; jnz +0x21
    code.extend(report(0x100c, 0x140, 54));
    code.extend([0x83, 0xfb, 0x03, 0x74, 0x25, 0x85, 0xdb, 0x74, 0x21]); // ASM: cmp ebx, 3; je +0x25; test ebx, ebx; jz +0x21
    code.extend(report(0x1036, 0x180, 61));
    code.extend([0x5b, 0xc3]); // ASM: pop rbx; ret
    let mut bytes = vec![0xccu8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let callee = rip(0x1100, &[0x8b, 0x05], 0x3000); // ASM: mov eax, [flag]
    bytes[0x100..0x106].copy_from_slice(&callee);
    bytes[0x106] = 0xc3; // ASM: ret
    bytes.extend(strings(last));
    bytes.resize(0x3000, 0);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", data, 0x1000, 0x1000, false, false),
            Section::mapped(".data", 0x3000, 0x2000, 0x1000, true, false),
        ],
    );
    p.symbols.push(Symbol {
        name: "libc!assert_fail".to_owned(),
        addr: data,
        kind: SymbolKind::Import,
    });
    p
}

/// Returns the arm64 `adrp rd, to; add rd, rd, lo12(to)` placed at `pc`.
///
/// # Arguments
///
/// * `pc` - Where the `adrp` is.
/// * `rd` - The register.
/// * `to` - The address it forms.
fn address_of(pc: u64, rd: u32, to: u64) -> [u32; 2] {
    let pages = lo32((to >> 12).wrapping_sub(pc >> 12));
    let adrp = 0x9000_0000 | ((pages & 3) << 29) | (((pages >> 2) & 0x7_ffff) << 5) | rd;
    [
        adrp,
        0x9100_0000 | (lo32(to & 0xfff) << 10) | (rd << 5) | rd,
    ]
}

/// Returns the arm64 words of a branch at `pc` to `to` under `op`, the
/// offset in words placed at `shift` and masked to `mask`.
///
/// # Arguments
///
/// * `op` - The instruction with a zero offset.
/// * `pc` - Where it is.
/// * `to` - Where it goes.
/// * `shift` - The offset field's lowest bit.
/// * `mask` - The offset field's width as a mask.
fn branch(op: u32, pc: u64, to: u64, shift: u32, mask: u32) -> u32 {
    op | ((lo32(to.wrapping_sub(pc) >> 2) & mask) << shift)
}

/// Returns an arm64 image of the reported function at 0x10000, its callee
/// reading a writable word, and a named reporter.
///
/// The function holds the same code as [`x64`], `w19` keeping the
/// parameter across the call.
///
/// # Arguments
///
/// * `last` - The text each assert passes in the function-name position.
fn arm64(last: &str) -> Program {
    let (base, data, callee, reporter) = (0x1_0000u64, 0x1_1000u64, 0x1_0100u64, 0x1_0180u64);
    let mut w: Vec<u32> = vec![0xa9be_7bfd, 0x9100_03fd, 0xf900_0bf3, 0x2a00_03f3]; // ASM: stp x29, x30, [sp, #-0x20]!; mov x29, sp; str x19, [sp, #0x10]; mov w19, w0
    let pc = |w: &Vec<u32>| base + 4 * from_usize(w.len());
    w.push(branch(0x9400_0000, pc(&w), callee, 0, 0x3ff_ffff)); // ASM: bl IsMainThread
    let skip1 = pc(&w) + 4 * 9;
    w.push(branch(0x3500_0000, pc(&w), skip1, 5, 0x7_ffff)); // ASM: cbnz w0, A
    let report = |w: &mut Vec<u32>, cond: u64, line: u32| {
        for (rd, to) in [(0, data + cond), (1, data + 0x100)] {
            let at = pc(w);
            w.extend(address_of(at, rd, to)); // ASM: adrp xN, s; add xN, xN, lo12(s)
        }
        w.push(0x5280_0002 | (line << 5)); // ASM: mov w2, line
        let at = pc(w);
        w.extend(address_of(at, 3, data + 0x200)); // ASM: adrp x3, last; add x3, x3, lo12(last)
        let at = pc(w);
        w.push(branch(0x9400_0000, at, reporter, 0, 0x3ff_ffff)); // ASM: bl assert_fail
    };
    report(&mut w, 0x140, 54);
    let done = pc(&w) + 4 * 11;
    w.push(0x7100_0e7f); // ASM: cmp w19, #3
    let at = pc(&w);
    w.push(branch(0x5400_0000, at, done, 5, 0x7_ffff)); // ASM: b.eq R
    let at = pc(&w);
    w.push(branch(0x3400_0013, at, done, 5, 0x7_ffff)); // ASM: cbz w19, R
    report(&mut w, 0x180, 61);
    w.extend([0xf940_0bf3, 0xa8c2_7bfd, 0xd65f_03c0]); // ASM: ldr x19, [sp, #0x10]; ldp x29, x30, [sp], #0x20; ret
    let mut code: Vec<u8> = w.iter().flat_map(|x| x.to_le_bytes()).collect();
    code.resize(0x100, 0);
    let flag = address_of(callee, 8, 0x1_2000);
    for x in [flag[0], 0xb940_0100, 0xd65f_03c0] {
        code.extend(x.to_le_bytes()); // ASM: adrp x8, flag; ldr w0, [x8]; ret
    }
    code.resize(0x180, 0);
    code.extend(0xd65f_03c0u32.to_le_bytes()); // ASM: ret (assert_fail)
    code.resize(0x1000, 0);
    code.extend(strings(last));
    code.resize(0x3000, 0);
    let mut p = Program::raw(
        code,
        Arch::Arm64,
        0,
        Some(base),
        vec![
            Section::mapped(".text", base, 0, 0x1000, false, true),
            Section::mapped(".rodata", data, 0x1000, 0x1000, false, false),
            Section::mapped(".data", 0x1_2000, 0x2000, 0x1000, true, false),
        ],
    );
    p.symbols.push(Symbol {
        name: "assert_fail".to_owned(),
        addr: reporter,
        kind: SymbolKind::Local,
    });
    p
}

/// Checks what the reported shape decompiles to on one target.
///
/// # Arguments
///
/// * `p` - The image, [`PRETTY`] in the function-name position.
/// * `entry` - The function.
/// * `callee` - The real `IsMainThread`.
fn the_pretty_function_names_it(p: &Program, entry: u64, callee: u64) {
    let a = Analysis::compute(p);
    let name = a.function(entry).and_then(|f| f.name.clone());
    assert_eq!(name.as_deref(), Some("audio::GetDefaultSourceArray"));
    assert_eq!(a.function(callee).and_then(|f| f.name.clone()), None);
    let text = decompile(p, &a, &Overlay::default(), entry).unwrap_or_default();
    let signature = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))
        .unwrap_or("");
    assert!(
        signature.starts_with("audio::SourceArray &audio::GetDefaultSourceArray(")
            && !signature.contains("this"),
        "{text}"
    );
    assert!(text.contains(&format!("\"{COND1}\"")), "{text}");
    assert!(text.contains("__FUNCSIG__"), "{text}");
    let header = answer_header(p, &a, &Overlay::default(), entry, None).unwrap_or_default();
    assert!(!header.contains("__FUNCSIG__"), "{header}");
    assert!(
        text.contains("// asserts: thread_util::IsMainThread(), false && 'Unsupported SourceType'"),
        "{text}"
    );
}

/// The reported shape names the function by the pretty-function string
/// both asserts pass, prints the condition as its literal, lists both
/// asserts and names nothing after the condition, on x64 and arm64.
#[test]
fn the_shared_pretty_function_names_the_asserting_function() {
    the_pretty_function_names_it(&x64(PRETTY), 0x1000, 0x1100);
    the_pretty_function_names_it(&arm64(PRETTY), 0x1_0000, 0x1_0100);
}

/// The unsure wording a name from a trace string carries.
const UNSURE: &str = "// name: unsure: a trace string only this function references";

/// Apple's assert passes the function's unqualified name beside the
/// condition, and the condition names nothing.
///
/// `__assert_rtn(__func__, file, line, "thread_util::IsMainThread()")`: the
/// name differs from the trace's last segment, on x64 and arm64.
#[test]
fn an_apple_assert_condition_names_nothing() {
    let func = "GetDefaultSourceArray";
    for (p, entry) in [(x64(func), 0x1000), (arm64(func), 0x1_0000)] {
        let a = Analysis::compute(&p);
        assert_eq!(a.function(entry).and_then(|f| f.name.clone()), None);
        let text = decompile(&p, &a, &Overlay::default(), entry).expect("decompiles");
        assert!(text.contains(&format!("\"{COND1}\"")), "{text}");
        assert!(!text.contains("__FUNCSIG__"), "{text}");
    }
}

/// A call-shaped string only one function references, with no full
/// signature and no name word beside it, names it with the unsure wording,
/// no types, no `this` and no `__FUNCSIG__`, on x64 and arm64.
#[test]
fn a_lone_trace_names_its_function_unsure() {
    let last = "(no name)";
    for (p, entry) in [(x64(last), 0x1000), (arm64(last), 0x1_0000)] {
        let a = Analysis::compute(&p);
        let f = a.function(entry).expect("a function");
        assert_eq!(f.name.as_deref(), Some("thread_util::IsMainThread"));
        assert!(f.signature.is_none());
        let header = answer_header(&p, &a, &Overlay::default(), entry, None).unwrap_or_default();
        assert!(header.lines().any(|l| l == UNSURE), "{header}");
        let text = decompile(&p, &a, &Overlay::default(), entry).expect("decompiles");
        let signature = text.lines().find(|l| l.starts_with("// signature: "));
        assert!(signature.is_some_and(|s| !s.contains("this")), "{text}");
        assert!(text.contains(&format!("\"{COND1}\"")), "{text}");
        assert!(!text.contains("__FUNCSIG__"), "{text}");
    }
}

/// The trace-like string at offset 0x240 of the data page.
///
/// A second candidate beside [`COND1`]; name words follow it,
/// `audio::Store` at 0x280, `audio::Load` at 0x2c0, `Load` at 0x300 and
/// `Store` at 0x320; the full signature `void audio::Load()` at 0x340.
const OTHER: &str = "audio::Load()";

/// Returns an x64 image whose `main` at 0x1000 calls one function per
/// entry of `funcs`, the k-th at 0x1100 + 0x40 k, each passing the
/// strings at its data offsets to the reporter one call each.
///
/// # Arguments
///
/// * `funcs` - Per function, the data-page offsets of the strings it passes.
fn reporters(funcs: &[&[u64]]) -> Program {
    let data = 0x2000u64;
    let mut bytes = vec![0xccu8; 0x1000];
    let mut main = Vec::new();
    for (k, offs) in (0u64..).zip(funcs) {
        let entry = 0x1100 + 0x40 * k;
        main.extend(rip(0x1000 + 5 * k, &[0xe8], entry)); // ASM: call function k
        let mut code = Vec::new();
        for off in *offs {
            let at = entry + from_usize(code.len());
            code.extend(rip(at, &[0x48, 0x8d, 0x0d], data + off)); // ASM: lea rcx, [string]
            code.extend(rip(at + 7, &[0xff, 0x15], data)); // ASM: call [reporter]
        }
        code.push(0xc3); // ASM: ret
        let at = usize::try_from(entry - 0x1000).unwrap_or(0);
        bytes[at..at + code.len()].copy_from_slice(&code);
    }
    main.push(0xc3); // ASM: ret
    bytes[..main.len()].copy_from_slice(&main);
    let mut page = strings(PRETTY);
    for (off, text) in [
        (0x240, OTHER),
        (0x280, "audio::Store"),
        (0x2c0, "audio::Load"),
        (0x300, "Load"),
        (0x320, "Store"),
        (0x340, "void audio::Load()"),
    ] {
        page[off..off + text.len()].copy_from_slice(text.as_bytes());
    }
    bytes.extend(page);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", data, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols.push(Symbol {
        name: "libc!assert_fail".to_owned(),
        addr: data,
        kind: SymbolKind::Import,
    });
    p
}

/// Returns the names of the functions [`reporters`] placed.
///
/// # Arguments
///
/// * `funcs` - As [`reporters`] takes them.
fn names(funcs: &[&[u64]]) -> Vec<Option<String>> {
    let p = reporters(funcs);
    let a = Analysis::compute(&p);
    (0u64..)
        .take(funcs.len())
        .map(|k| a.function(0x1100 + 0x40 * k).and_then(|f| f.name.clone()))
        .collect()
}

/// Condition text two functions reference names neither; a full signature
/// beside a call-shaped string wins; two call-shaped strings name nothing.
#[test]
fn a_trace_names_only_the_one_function_with_no_better_evidence() {
    assert_eq!(names(&[&[0x140], &[0x140]]), [None, None]);
    assert_eq!(
        names(&[&[0x140, 0x200]]),
        [Some("audio::GetDefaultSourceArray".to_owned())]
    );
    assert_eq!(names(&[&[0x140, 0x240]]), [None]);
    assert_eq!(names(&[&[0x240]]), [Some("audio::Load".to_owned())]);
}

/// A bare `__FUNCTION__`-style name or a `__func__`-style identifier that
/// differs from the trace blocks it, and one that agrees keeps it.
#[test]
fn a_bare_function_name_decides_a_trace() {
    assert_eq!(names(&[&[0x240, 0x280]]), [None]);
    assert_eq!(names(&[&[0x240, 0x2c0]]), [Some("audio::Load".to_owned())]);
    assert_eq!(names(&[&[0x280]]), [None]);
    assert_eq!(names(&[&[0x240, 0x320]]), [None]);
    assert_eq!(names(&[&[0x240, 0x300]]), [Some("audio::Load".to_owned())]);
}

/// A full signature of the trace's name anywhere proves the trace a call:
/// the trace names nothing and the signature's function takes the name
/// unnumbered, whichever comes first.
#[test]
fn a_full_signature_elsewhere_outranks_a_trace() {
    let load = Some("audio::Load".to_owned());
    assert_eq!(names(&[&[0x240], &[0x340]]), [None, load.clone()]);
    assert_eq!(names(&[&[0x340], &[0x240]]), [load, None]);
}

/// An exported pack leaves a trace name out and says so, so loading the
/// pack back names nothing for certain that the program only guessed.
#[test]
fn a_trace_name_stays_out_of_an_exported_pack() {
    use borer_engine::analysis::NameSource;
    use borer_engine::analysis::sigs::export_pack;
    use borer_engine::pack::{Pack, Packs};
    let p = reporters(&[&[0x240]]);
    let a = Analysis::compute(&p);
    let f = a.function(0x1100).expect("a function");
    assert_eq!(f.name_source, NameSource::Trace);
    let text = export_pack(&p, &a, &Overlay::default(), "probe", true);
    assert!(!text.contains("audio::Load"), "{text}");
    assert!(
        text.contains("# 1 names read from a trace string are left out"),
        "{text}"
    );
    let (pack, _) = Pack::parse(&text, "probe.borer").expect("the export reads");
    let b = Analysis::compute_with(&p, std::sync::Arc::new(Packs { packs: vec![pack] }));
    let f = b.function(0x1100).expect("a function");
    assert_eq!(f.name_source, NameSource::Trace);
}

/// The first bytes of a [`reporters`] function passing one string, its
/// displacements wildcarded.
const ONE_CALL: &str = "488D0D????????FF15????????C3";

/// The first bytes of a [`reporters`] function passing two strings.
const TWO_CALLS: &str = "488D0D????????FF15????????488D0D????????FF15????????C3";

/// Returns the analysis of `p` with a pack naming functions by their first
/// bytes loaded.
///
/// # Arguments
///
/// * `p` - The image.
/// * `lines` - Each function's first bytes and the name the pack gives it.
fn with_pack(p: &Program, lines: &[(&str, &str)]) -> Analysis {
    use borer_engine::pack::{Pack, Packs};
    let mut text = "pack probe 1\nabout names by first bytes\n\n[names]\n".to_owned();
    for (bytes, name) in lines {
        text.push_str(&format!("fn {bytes} {name}\n"));
    }
    let pack = Pack::parse(&text, "probe.borer").map_or_else(|_| None, |(pack, _)| Some(pack));
    let packs = Packs {
        packs: pack.into_iter().collect(),
    };
    Analysis::compute_with(p, std::sync::Arc::new(packs))
}

/// A trace name is the weakest: a pack naming its function replaces it,
/// and a pack giving another function the trace's text removes it.
#[test]
fn a_later_name_outranks_a_trace() {
    use borer_engine::analysis::NameSource;
    let p = reporters(&[&[0x240]]);
    let a = with_pack(&p, &[(ONE_CALL, "audio::Real")]);
    let f = a.function(0x1100).expect("a function");
    assert_eq!(
        (f.name.as_deref(), f.name_source),
        (Some("audio::Real"), NameSource::Pack)
    );
    let p = reporters(&[&[0x240], &[0x2c0, 0x320]]);
    let a = with_pack(&p, &[(TWO_CALLS, "audio::Load")]);
    let names = |e: u64| a.function(e).and_then(|f| f.name.clone());
    assert_eq!(names(0x1140).as_deref(), Some("audio::Load"));
    assert_eq!(names(0x1100), None);
}
