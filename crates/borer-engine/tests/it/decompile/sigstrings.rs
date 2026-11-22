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

use borer_engine::analysis::decompile::decompile;
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

/// A function whose only candidate is call-expression condition text takes
/// no name from it and prints it as the literal.
#[test]
fn condition_text_alone_names_nothing() {
    for (p, entry) in [(x64("audio"), 0x1000), (arm64("audio"), 0x1_0000)] {
        let a = Analysis::compute(&p);
        assert_eq!(a.function(entry).and_then(|f| f.name.clone()), None);
        let text = decompile(&p, &a, &Overlay::default(), entry).expect("decompiles");
        assert!(text.contains(&format!("\"{COND1}\"")), "{text}");
        assert!(!text.contains("__FUNCSIG__"), "{text}");
    }
}
