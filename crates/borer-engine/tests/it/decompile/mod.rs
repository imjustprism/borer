//! Decompiler tests on the shared fixture (see `common`).

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::common;
use crate::decompiled;
use crate::fixture_pack;

use borer_engine::analysis::decompile::enum_table;
use borer_engine::analysis::{
    Analysis, EnumSource, Overlay,
    decompile::{
        asserts_of, cleanup, decompile, decompile_all, decompile_scenario, enum_tables,
        enums_by_name, polish, skeleton,
    },
};
use common::fixture;
use decompiled::{decompiled, program64, program64_with_data, replays_clean, runs_agree};
use fixture_pack::fixture_pack;

mod calls;
mod classes;
mod floats;
mod flow;
mod lanes;
mod results;
mod rounding;
mod solve;
mod switches;
mod values;

/// Decompiles one fixture function with an empty overlay.
///
/// # Arguments
///
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The pseudo-C, or an empty string when decompilation fails.
fn dc(entry: u64) -> String {
    decompiled(&fixture(), entry)
}

/// Decompiles one fixture function with the test pack loaded.
fn dc_pack(entry: u64) -> String {
    let p = fixture();
    let a = Analysis::compute_with(&p, fixture_pack());
    decompile(&p, &a, &Overlay::default(), entry).unwrap_or_default()
}

/// A 32-bit image of `code` at `0x401000`, entered at its start.
///
/// # Arguments
///
/// * `code` - The bytes.
fn program32(code: &[u8]) -> borer_engine::program::Program {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    p
}

/// Builds a 64-bit program of `code` with an `.rdata` page of `data` and
/// an import symbol at each given address table slot.
///
/// # Arguments
///
/// * `code` - The bytes of `.text` at 0x140001000.
/// * `data` - The bytes of `.rdata` at 0x140002000.
/// * `imports` - `(slot, "DLL!name")` per import.
fn program64_with_imports(
    code: &[u8],
    data: &[u8],
    imports: &[(u64, &str)],
) -> borer_engine::program::Program {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut p = program64_with_data(code, data);
    p.symbols = imports
        .iter()
        .map(|(addr, name)| Symbol {
            name: (*name).to_owned(),
            addr: *addr,
            kind: SymbolKind::Import,
        })
        .collect();
    p
}

/// Builds the `.rdata` bytes of a table of signed 32-bit offsets from
/// `base` to each of `targets`.
///
/// # Arguments
///
/// * `base` - What every entry is relative to.
/// * `targets` - The case addresses, in table order.
///
/// # Returns
///
/// The entries, little-endian, followed by nothing.
#[expect(
    clippy::unwrap_used,
    reason = "a fixture builder: every target is within 2 GB of its base"
)]
fn rel32_entries(base: u64, targets: &[u64]) -> Vec<u8> {
    targets
        .iter()
        .flat_map(|&t| {
            i32::try_from(t.cast_signed() - base.cast_signed())
                .unwrap()
                .to_le_bytes()
        })
        .collect()
}

/// Builds a 64-bit ELF image with `code` in `.text` at 0x140001000,
/// entered there, a writable data page at 0x140003000, and data symbols
/// naming addresses in it.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, at most a page.
/// * `zero_filled` - The data page is a `.bss` the file holds no bytes
///   for, rather than a `.data` it does.
/// * `symbols` - `(name, address)` of each data symbol.
fn program64_with_globals(
    code: &[u8],
    zero_filled: bool,
    symbols: &[(&str, u64)],
) -> borer_engine::program::Program {
    use borer_engine::program::{
        Arch, BinaryFormat, FileOff, Program, Section, Symbol, SymbolKind, Va,
    };
    let mut bytes = vec![0u8; 0x2000];
    bytes[..code.len()].copy_from_slice(code);
    let data = Section {
        name: if zero_filled { ".bss" } else { ".data" }.to_owned(),
        va: Va(0x1_4000_3000),
        vsize: 0x1000,
        file_off: FileOff(if zero_filled { 0 } else { 0x1000 }),
        file_size: if zero_filled { 0 } else { 0x1000 },
        readable: true,
        writable: true,
        executable: false,
    };
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![
            Section::mapped(".text", 0x1_4000_1000, 0, 0x1000, false, true),
            data,
        ],
    );
    p.format = BinaryFormat::Elf;
    p.symbols = symbols
        .iter()
        .map(|&(name, addr)| Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Data,
        })
        .collect();
    p
}

/// `mov rax,[rip+0x1ff9]; ret`: returns the word at 0x140003000.
const READ_GLOBAL: [u8; 8] = [
    0x48, 0x8b, 0x05, 0xf9, 0x1f, 0x00, 0x00, // ASM: mov rax,[rip+0x1ff9]
    0xc3, // ASM: ret
];
