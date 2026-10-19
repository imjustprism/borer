//! Which instruction set ARM32 code is in, read from what the file says:
//! the interworking bit on an entry point or a function's address, and an
//! ELF's mapping symbols.
//!
//! A32 and T32 code mix in one image, and an address names a T32
//! function with its low bit set (an ELF `STT_FUNC` symbol, a Windows
//! export and entry point, a Mach-O symbol the loader marks so). The
//! loader clears that bit, so every address the engine holds is the
//! instruction's own, and records the instruction set instead
//! ([`crate::isa::a32::Modes`]).

use super::{Section, Symbol, SymbolKind};
use crate::isa::a32::{Mode, Modes};

/// What [`settle`] reads and clears the interworking bit on.
pub(super) struct Code<'a> {
    /// The entry point.
    pub entry: &'a mut Option<u64>,
    /// The symbols.
    pub symbols: &'a mut [Symbol],
    /// The function extents the file declares.
    pub ranges: &'a mut [(u64, u64)],
    /// The sections, for which addresses hold code.
    pub sections: &'a [Section],
}

/// Reads an ELF's mapping symbols: `$a` opens A32 code, `$t` T32 code
/// (each also with a `.n` suffix); `$d` data, which names no instruction
/// set.
///
/// # Arguments
///
/// * `elf` - The parsed file.
///
/// # Returns
///
/// The marks, in file order.
pub(super) fn mapping_symbols(elf: &goblin::elf::Elf<'_>) -> Vec<(u64, Mode)> {
    elf.syms
        .iter()
        .filter(|s| goblin::elf::sym::st_type(s.st_info) == goblin::elf::sym::STT_NOTYPE)
        .filter_map(|s| {
            let name = elf.strtab.get_at(s.st_name)?;
            let base = name.split('.').next().unwrap_or(name);
            let mode = match base {
                "$a" => Mode::Arm,
                "$t" => Mode::Thumb,
                _ => return None,
            };
            Some((s.st_value, mode))
        })
        .collect()
}

/// Clears the interworking bit from the entry point, the code symbols and
/// the declared extents, and returns which instruction set each stretch of
/// code is in.
///
/// An odd address in an executable section names T32 code at the address
/// below it; an even one, A32 code, unless the mapping symbols already
/// say. Code no mark covers is in `default`.
///
/// # Arguments
///
/// * `code` - The addresses to settle.
/// * `mapping` - The marks the file states outright, which win.
/// * `default` - The instruction set of code nothing marks.
pub(super) fn settle(code: &mut Code<'_>, mapping: &[(u64, Mode)], default: Mode) -> Modes {
    let executable = |va: u64| {
        code.sections
            .iter()
            .any(|s| s.executable && va >= s.va.0 && va - s.va.0 < s.vsize)
    };
    let mut marks = mapping.to_vec();
    marks.push((0, default));
    let settle_one = |va: &mut u64, marks: &mut Vec<(u64, Mode)>| {
        if *va & 1 == 1 && executable(*va - 1) {
            *va -= 1;
            marks.push((*va, Mode::Thumb));
        } else if executable(*va) {
            marks.push((*va, Mode::Arm));
        }
    };
    let mut symbol_marks = Vec::new();
    if let Some(e) = code.entry.as_mut() {
        settle_one(e, &mut symbol_marks);
    }
    for s in code.symbols.iter_mut() {
        if matches!(s.kind, SymbolKind::Export | SymbolKind::Local) {
            settle_one(&mut s.addr, &mut symbol_marks);
        }
    }
    for r in code.ranges.iter_mut() {
        if r.0 & 1 == 1 && executable(r.0 - 1) {
            r.0 -= 1;
            r.1 = r.1.saturating_sub(1);
        }
    }
    let stated = marks.len() > 1;
    marks.extend(
        symbol_marks
            .into_iter()
            .filter(|&(_, m)| !stated || m == Mode::Thumb),
    );
    Modes::from_marks(marks)
}
