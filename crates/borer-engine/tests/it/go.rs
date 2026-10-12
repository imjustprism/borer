//! Go's function table and register ABI.
//!
//! A Go binary names every function in its `pclntab`, stripped or not. The
//! table is read from its `.gopclntab` section, or found by its magic where
//! no section names it, and a corrupt one is refused. The functions it
//! lists take their arguments in Go's registers (`rax`, `rbx`, `rcx`, ...),
//! and their stack-growth prologue folds into one comment.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use crate::elfgen::{self, A, AX, EM_X86_64, ET_EXEC, PROGBITS, Sec};
use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::render::{emulate_tsv, why_tsv};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::go::GoVersion;
use borer_engine::program::{Program, SymbolKind};

/// `main.main`: the stack check, then `return 0`.
const MAIN: u64 = 0x1000;
/// `main.add`: `lea rax,[rax+rbx]; ret`, Go's `a + b`.
const ADD: u64 = 0x1010;
/// `runtime.morestack_noctxt`: `ret`.
const MORESTACK: u64 = 0x1030;

/// The functions the table lists, as `(offset from the text, name)`.
const FUNCS: [(u32, &str); 3] = [
    (0x00, "main.main"),
    (0x10, "main.add"),
    (0x30, "runtime.morestack_noctxt"),
];

/// Bytes in one Go 1.20 `_func` record.
const RECORD: usize = 44;

/// A Go 1.20 `pclntab` over a text at `0x1000`, for 64-bit pointers.
///
/// The header, the function name table, then the function table (an entry
/// offset and a record offset per function, and the end of the text) and
/// the records, each stating its entry offset and its name's offset.
///
/// # Arguments
///
/// * `funcs` - The functions, as `(offset from the text, name)`.
/// * `end` - The text's end, as an offset.
fn pclntab(funcs: &[(u32, &str)], end: u32) -> Vec<u8> {
    let mut names = Vec::new();
    let mut name_offs = Vec::new();
    for (_, name) in funcs {
        name_offs.push(u32::try_from(names.len()).expect("fits"));
        names.extend_from_slice(name.as_bytes());
        names.push(0);
    }
    let pcln = (72 + names.len()).next_multiple_of(8);
    let functab = (funcs.len() + 1) * 8;
    let mut out = vec![0u8; pcln + functab + funcs.len() * RECORD];
    out[0..8].copy_from_slice(&[0xf1, 0xff, 0xff, 0xff, 0, 0, 1, 8]);
    let pcln64 = u64::try_from(pcln).expect("fits");
    for (k, v) in [
        u64::try_from(funcs.len()).expect("fits"),
        0,
        MAIN,
        72,
        pcln64,
        pcln64,
        pcln64,
        pcln64,
    ]
    .iter()
    .enumerate()
    {
        out[8 + k * 8..16 + k * 8].copy_from_slice(&v.to_le_bytes());
    }
    out[72..72 + names.len()].copy_from_slice(&names);
    for (i, (entry, _)) in funcs.iter().enumerate() {
        let record = functab + i * RECORD;
        out[pcln + i * 8..pcln + i * 8 + 4].copy_from_slice(&entry.to_le_bytes());
        out[pcln + i * 8 + 4..pcln + i * 8 + 8]
            .copy_from_slice(&u32::try_from(record).expect("fits").to_le_bytes());
        out[pcln + record..pcln + record + 4].copy_from_slice(&entry.to_le_bytes());
        out[pcln + record + 4..pcln + record + 8].copy_from_slice(&name_offs[i].to_le_bytes());
    }
    let last = pcln + funcs.len() * 8;
    out[last..last + 4].copy_from_slice(&end.to_le_bytes());
    out
}

/// A stripped Go executable: the three functions in `.text`, and the table
/// in a section of the given name at `0x2000`, `lead` bytes in.
///
/// # Arguments
///
/// * `section` - The table's section name.
/// * `lead` - Bytes before the table in that section.
/// * `table` - The table.
fn go_elf(section: &'static str, lead: usize, table: &[u8]) -> Program {
    let mut text = vec![0xccu8; 0x31];
    let code: [(usize, &[u8]); 7] = [
        (0x00, &[0x49, 0x3b, 0x66, 0x10]),       // ASM: cmp rsp,[r14+0x10]
        (0x04, &[0x76, 0x03]),                   // ASM: jbe 0x1009
        (0x06, &[0x31, 0xc0, 0xc3]),             // ASM: xor eax,eax; ret
        (0x09, &[0xe8, 0x22, 0, 0, 0]),          // ASM: call 0x1030 (runtime.morestack_noctxt)
        (0x0e, &[0xeb, 0xf0]),                   // ASM: jmp 0x1000
        (0x10, &[0x48, 0x8d, 0x04, 0x18, 0xc3]), // ASM: lea rax,[rax+rbx]; ret
        (0x30, &[0xc3]),                         // ASM: ret
    ];
    for (at, bytes) in code {
        text[at..at + bytes.len()].copy_from_slice(bytes);
    }
    let mut data = vec![0x5au8; lead];
    data.extend_from_slice(table);
    let bytes = elfgen::build(
        ET_EXEC,
        EM_X86_64,
        MAIN,
        &[
            Sec::new(".text", PROGBITS, AX, 0x1000, text),
            Sec::new(section, PROGBITS, A, 0x2000, data),
        ],
    );
    Program::from_bytes(std::path::PathBuf::from("go.elf"), bytes).expect("the image loads")
}

/// The names `pclntab` gives the program, as `(address, name)`.
///
/// # Arguments
///
/// * `p` - The program.
fn locals(p: &Program) -> Vec<(u64, &str)> {
    p.symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Local)
        .map(|s| (s.addr, s.name.as_str()))
        .collect()
}

/// A Go 1.20 table in `.gopclntab` names every function it lists, and
/// `why` says the name came from it.
#[test]
fn a_gopclntab_section_names_its_functions() {
    let p = go_elf(".gopclntab", 0, &pclntab(&FUNCS, 0x31));
    assert_eq!(
        locals(&p),
        vec![
            (MAIN, "main.main"),
            (ADD, "main.add"),
            (MORESTACK, "runtime.morestack_noctxt")
        ]
    );
    let go = p.go.as_ref().expect("the table is kept");
    assert_eq!(go.version, GoVersion::V1_20);
    assert_eq!(go.at, 0x2000);
    assert!(
        p.summary()
            .contains("go:      pclntab of Go 1.20+ at 0x2000: 3 functions named\n"),
        "{}",
        p.summary()
    );
    let a = Analysis::compute(&p);
    let why = why_tsv(&p, &a, &Overlay::default(), "main.add").expect("main.add resolves");
    assert!(
        why.contains("# name: the Go function table (pclntab, Go 1.20+) records it: main.add\n"),
        "{why}"
    );
}

/// The same table in a section no toolchain names, past some other data,
/// is found by its magic.
#[test]
fn a_table_in_an_unnamed_section_is_found_by_its_magic() {
    let p = go_elf(".rodata", 0x24, &pclntab(&FUNCS, 0x31));
    assert_eq!(p.go.as_ref().map(|g| g.at), Some(0x2024));
    assert_eq!(locals(&p).len(), 3, "{:?}", locals(&p));
}

/// A corrupt table names nothing: a record that disagrees with its entry,
/// entries out of order, a name past the table, or a count past the end
/// each refuse the whole table.
#[test]
fn a_corrupt_table_is_refused() {
    let good = pclntab(&FUNCS, 0x31);
    let pcln = (72 + FUNCS.iter().map(|f| f.1.len() + 1).sum::<usize>()).next_multiple_of(8);
    let mut mismatch = good.clone();
    let record = pcln + 4 * 8 + RECORD;
    mismatch[record] = 0x11;
    let unordered = pclntab(&[(0x10, "main.add"), (0x00, "main.main")], 0x31);
    let mut far_name = good.clone();
    far_name[record + 4..record + 8].copy_from_slice(&0xffffu32.to_le_bytes());
    let mut count = good.clone();
    count[8..16].copy_from_slice(&(1u64 << 40).to_le_bytes());
    let mut truncated = good;
    truncated.truncate(pcln + 8);
    for (what, table) in [
        ("a record that disagrees", mismatch),
        ("entries out of order", unordered),
        ("a name past the table", far_name),
        ("a count past the end", count),
        ("a truncated table", truncated),
    ] {
        for section in [".gopclntab", ".rodata"] {
            let p = go_elf(section, 0, &table);
            assert!(p.go.is_none(), "{what} in {section} was read");
            assert!(
                locals(&p).is_empty(),
                "{what} in {section}: {:?}",
                locals(&p)
            );
        }
    }
}

/// A function the table lists takes its arguments in Go's registers:
/// `main.add` reads `rbx` as its second argument, so it decompiles with
/// `a2`, and `emulate`'s `a2=` sets `rbx`.
///
/// Read by System V, `rbx` is a register the callee keeps, not an
/// argument, and the signature had none.
#[test]
fn a_go_function_takes_rbx_as_its_second_argument() {
    let p = go_elf(".gopclntab", 0, &pclntab(&FUNCS, 0x31));
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, ADD).expect("main.add decompiles");
    let signature = text
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .expect("a signature line");
    assert!(
        signature.contains("a1") && signature.contains("a2"),
        "{text}"
    );
    assert!(
        text.contains("a1 + a2") || text.contains("a2 + a1"),
        "{text}"
    );
    let run = emulate_tsv(&p, &a, &o, "main.add,a1=2,a2=3").expect("main.add runs");
    assert!(run.contains("rax=0x5 "), "{run}");
}

/// The stack-growth prologue, `cmp rsp,[r14+0x10]; jbe` to a block that
/// calls `runtime.morestack_noctxt`, folds into one comment: the body is
/// what runs once the stack is big enough.
#[test]
fn the_stack_check_folds_into_one_comment() {
    let p = go_elf(".gopclntab", 0, &pclntab(&FUNCS, 0x31));
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), MAIN).expect("main.main decompiles");
    assert!(
        text.contains(
            "// go stack check folded: cmp rsp, [r14+0x10]; jbe runtime.morestack_noctxt\n"
        ),
        "{text}"
    );
    assert!(text.contains("return 0;"), "{text}");
    assert!(!text.contains("if ("), "{text}");
    assert!(!text.contains("morestack_noctxt()"), "{text}");
}
