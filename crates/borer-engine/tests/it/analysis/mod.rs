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

mod classes;
mod diff;
mod functions;
mod graph;
mod hints;
mod memo;
mod owner;
mod protection;
mod unpack;
mod votes;

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
