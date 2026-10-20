//! Syscall sites of static Linux binaries.
//!
//! A static ELF imports nothing; its reach is the kernel calls it makes.
//! `mov eax, N; syscall` (x86-64), `int 0x80` with `eax` (i386) and
//! `svc #0` with `x8` (arm64) are tagged with the call's name, in the
//! listing and the summary, and count toward the capability map the way
//! imports do; a number set outside the block is unresolved.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use crate::elfgen::{self, AX, EM_X86_64, ET_EXEC, PROGBITS, Sec};
use borer_engine::analysis::decompile::{checked_header, decompile};
use borer_engine::analysis::render::{capability_map_tsv, disasm_function, function_summary};
use borer_engine::analysis::syscalls::{Gate, syscall_sites};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

/// A static x86-64 ELF whose entry opens a socket, connects it and runs a
/// program through `syscall`, then makes one more with `eax` copied from
/// `edi`.
fn static_x64() -> Program {
    let code: &[u8] = &[
        0xb8, 0x29, 0x00, 0x00, 0x00, // ASM: mov eax,41
        0xbf, 0x02, 0x00, 0x00, 0x00, // ASM: mov edi,2
        0xbe, 0x01, 0x00, 0x00, 0x00, // ASM: mov esi,1
        0x31, 0xd2, // ASM: xor edx,edx
        0x0f, 0x05, // ASM: syscall
        0x89, 0xc7, // ASM: mov edi,eax
        0xb8, 0x2a, 0x00, 0x00, 0x00, // ASM: mov eax,42
        0x0f, 0x05, // ASM: syscall
        0x6a, 0x3b, // ASM: push 59
        0x58, // ASM: pop rax
        0x0f, 0x05, // ASM: syscall
        0x89, 0xf8, // ASM: mov eax,edi
        0x0f, 0x05, // ASM: syscall
        0xc3, // ASM: ret
    ];
    let bytes = elfgen::build(
        ET_EXEC,
        EM_X86_64,
        0x1000,
        &[Sec::new(".text", PROGBITS, AX, 0x1000, code.to_vec())],
    );
    Program::from_bytes(std::path::PathBuf::from("static.elf"), bytes).expect("the image loads")
}

/// A headerless image of `code` at 0x1000 read as an ELF of `arch`.
///
/// # Arguments
///
/// * `arch` - The instruction set.
/// * `code` - The code.
fn raw_elf(arch: Arch, code: &[u8]) -> Program {
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        arch,
        0,
        Some(0x1000),
        vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Elf;
    p
}

/// The sites as `(address, gate, number, name)`.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - Its analysis.
fn sites(p: &Program, a: &Analysis) -> Vec<(u64, Gate, Option<u64>, Option<&'static str>)> {
    syscall_sites(p, a)
        .iter()
        .map(|s| (s.at, s.gate, s.nr, s.name))
        .collect()
}

/// `mov eax, N; syscall` is tagged `syscall` with its name, a number set
/// by `push N; pop rax` too, and one copied from another register is
/// unresolved, not guessed.
#[test]
fn a_syscall_is_tagged_with_its_name() {
    let p = static_x64();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        sites(&p, &a),
        vec![
            (0x1011, Gate::Syscall, Some(41), Some("socket")),
            (0x101a, Gate::Syscall, Some(42), Some("connect")),
            (0x101f, Gate::Syscall, Some(59), Some("execve")),
            (0x1023, Gate::Syscall, None, None),
        ]
    );
    let listing = disasm_function(&p, &a, &o, 0x1000, 64, false).expect("a listing");
    assert!(
        listing.contains("0x1011  syscall  ; syscall socket\n"),
        "{listing}"
    );
    assert!(
        listing.contains("0x1023  syscall  ; syscall ?\n"),
        "{listing}"
    );
    let summary = function_summary(&p, &a, &o, 0x1000).expect("a summary");
    assert!(
        summary.contains("syscall connect") && summary.contains("syscall execve"),
        "{summary}"
    );
}

/// A static ELF with no imports reports network and process capability
/// from its `socket`, `connect` and `execve` syscalls.
///
/// Read from its imports alone it reported no capability at all.
#[test]
fn static_syscalls_report_network_capability() {
    let p = static_x64();
    let a = Analysis::compute(&p);
    let map = capability_map_tsv(&p, Some(&a));
    assert!(
        map.starts_with(
            "# 2 of 16 capabilities present across 0 imports and 4 syscall sites (1 whose number its block does not set)\n"
        ),
        "{map}"
    );
    assert!(
        map.contains("networking                connect (syscall), socket (syscall)\n"),
        "{map}"
    );
    assert!(
        map.contains("process control           execve (syscall)\n"),
        "{map}"
    );
    assert!(
        capability_map_tsv(&p, None).starts_with("# 0 of 16 capabilities"),
        "the imports alone say nothing"
    );
}

/// `int 0x80` reads its number from `eax` by the i386 table, and arm64's
/// `svc #0` from `x8` by the generic one.
#[test]
fn int_0x80_and_svc_are_tagged_by_their_tables() {
    let i386 = raw_elf(
        Arch::X86,
        &[
            0xb8, 0x67, 0x01, 0x00, 0x00, // ASM: mov eax,359
            0xcd, 0x80, // ASM: int 0x80
            0xb8, 0x66, 0x00, 0x00, 0x00, // ASM: mov eax,102
            0xcd, 0x80, // ASM: int 0x80
            0xc3, // ASM: ret
        ],
    );
    let a = Analysis::compute(&i386);
    assert_eq!(
        sites(&i386, &a),
        vec![
            (0x1005, Gate::Int80, Some(359), Some("socket")),
            (0x100c, Gate::Int80, Some(102), Some("socketcall")),
        ]
    );
    let arm64 = raw_elf(
        Arch::Arm64,
        &[
            0xc8, 0x18, 0x80, 0x52, // ASM: mov w8,#198
            0x01, 0x00, 0x00, 0xd4, // ASM: svc #0
            0x68, 0x19, 0x80, 0x52, // ASM: mov w8,#203
            0x01, 0x00, 0x00, 0xd4, // ASM: svc #0
            0xc0, 0x03, 0x5f, 0xd6, // ASM: ret
        ],
    );
    let a = Analysis::compute(&arm64);
    assert_eq!(
        sites(&arm64, &a),
        vec![
            (0x1004, Gate::Svc, Some(198), Some("socket")),
            (0x100c, Gate::Svc, Some(203), Some("connect")),
        ]
    );
}

/// A Linux `syscall` decompiles as the call its number names, with the
/// arguments the C library's function of that name takes, from the
/// registers the kernel reads them from.
///
/// The kernel leaves the argument registers alone, so `connect` and
/// `execve` still read the `1` and `0` set for `socket`, and both read the
/// descriptor `socket` returned. A number copied from `edi` is named by no
/// table and stays the C library's `syscall(nr, ...)`.
#[test]
fn syscalls_decompile_as_the_calls_they_name() {
    let p = static_x64();
    let a = Analysis::compute(&p);
    let out = decompile(&p, &a, &Overlay::default(), 0x1000).expect("the entry decompiles");
    assert!(
        out.contains("s = socket(AF_INET, SOCK_STREAM, IPPROTO_IP);"),
        "{out}"
    );
    assert!(out.contains("connect(s, 1, 0);"), "{out}");
    assert!(out.contains("execve(FileName, 1, NULL);"), "{out}");
    assert!(out.contains("return syscall(FileName);"), "{out}");
    assert!(!out.contains("undeclared"), "{out}");
    let header = checked_header(&p, &a, &Overlay::default(), 0x1000).unwrap_or_default();
    assert!(header.contains("checked vs binary"), "{header}");
    assert!(!header.contains("differ"), "{header}");
}
