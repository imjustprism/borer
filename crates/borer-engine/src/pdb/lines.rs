//! PDB source-line resolution: picking each procedure's first line row and
//! naming its file from the string table.

use super::Gathered;
use std::collections::BTreeMap;
use std::io::Cursor;

/// Tracks module-stream line eligibility across [`super::gather`]'s DBI walk.
#[derive(Debug, Default)]
pub(super) struct LineReader {
    /// Whether the caller asked for line programs (`sources` vs `apply`).
    want: bool,
    /// Per-module `module_line_flags` result aligned with `dbi.modules()`.
    flags: Vec<bool>,
    /// Index of the next module yielded by `dbi.modules()`.
    next: usize,
}

impl LineReader {
    /// Prepares line-program tracking for one [`super::gather`] pass.
    ///
    /// # Arguments
    ///
    /// * `db` - The opened PDB.
    /// * `want` - Whether to read module line programs.
    ///
    /// # Returns
    ///
    /// A reader aligned with the first module of `db.debug_information()`.
    pub(super) fn new<'s>(db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>, want: bool) -> Self {
        let flags = if want {
            super::streams::module_line_flags(db)
        } else {
            Vec::new()
        };
        Self {
            want,
            flags,
            next: 0,
        }
    }

    /// Opens `m`'s module stream and reports whether its line program may be read.
    ///
    /// # Arguments
    ///
    /// * `db` - The opened PDB.
    /// * `m` - Next module yielded by `dbi.modules()`.
    ///
    /// # Returns
    ///
    /// The module's symbol and line stream paired with whether `line_program()`
    /// is wanted and within bounds, or `None` when `m` carries no readable stream.
    pub(super) fn open<'s>(
        &mut self,
        db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
        m: &pdb::Module<'_>,
    ) -> Option<(pdb::ModuleInfo<'s>, bool)> {
        let idx = self.next;
        self.next += 1;
        let info = db.module_info(m).ok()??;
        let ok = self.want && self.flags.get(idx).copied().unwrap_or(false);
        Some((info, ok))
    }
}

impl Gathered {
    /// Reads `info`'s line program when `lines_ok` holds and records each procedure's first row.
    ///
    /// # Arguments
    ///
    /// * `info` - The module's symbol and line stream.
    /// * `lines_ok` - Whether line programs are requested and readable for this module.
    /// * `map` - Address map translating internal section offsets to RVAs.
    /// * `guard` - Checked RVA translation guard.
    /// * `procs` - Procedures gathered from this module.
    pub(super) fn collect_module_lines(
        &mut self,
        info: &pdb::ModuleInfo<'_>,
        lines_ok: bool,
        map: &pdb::AddressMap<'_>,
        guard: &super::streams::AddrGuard,
        procs: &[(u32, pdb::PdbInternalSectionOffset)],
    ) {
        if lines_ok
            && !procs.is_empty()
            && let Ok(program) = info.line_program()
        {
            self.take_lines(&program, map, guard, procs);
        }
    }

    /// Takes the first line row each stated procedure starts at.
    ///
    /// Rows are asked of the module's own program by the offset its
    /// records state, and are not promised to be in offset order, so the
    /// winner is the row with the least offset inside the procedure's
    /// extent, ties by the lesser line. Only a procedure the gather sized
    /// has an extent to place rows in; a row outside it, a zero line, or a
    /// file the program does not name contributes nothing.
    ///
    /// # Arguments
    ///
    /// * `program` - The module's line program.
    /// * `map` - The address map, translating the internal offsets the
    ///   rows state into image RVAs.
    /// * `guard` - Checked RVA translation guard.
    /// * `procs` - The procedures this module states, RVA and record
    ///   offset.
    fn take_lines(
        &mut self,
        program: &pdb::LineProgram<'_>,
        map: &pdb::AddressMap<'_>,
        guard: &super::streams::AddrGuard,
        procs: &[(u32, pdb::PdbInternalSectionOffset)],
    ) {
        use pdb::FallibleIterator as _;
        for &(rva, offset) in procs {
            let Some(&end) = self.extents.get(&rva) else {
                continue;
            };
            let mut rows = program.lines_for_symbol(offset);
            while let Ok(Some(row)) = rows.next() {
                let Some(at) = guard.rva_of(map, row.offset) else {
                    continue;
                };
                if at < rva || at >= end || row.line_start == 0 {
                    continue;
                }
                if self.lines.get(&rva).is_some_and(|&(best, _, line)| {
                    best < at || (best == at && line <= row.line_start)
                }) {
                    continue;
                }
                if let Ok(file) = program.get_file_info(row.file_index) {
                    self.lines.insert(rva, (at, file.name, row.line_start));
                }
            }
        }
    }
}

/// Reads the source file and line each gathered procedure starts at, from
/// the modules' line programs.
///
/// One row per procedure: the first line row the module's program maps
/// inside the procedure's extent, which is the line its first instruction
/// was written on. A name the string table does not hold contributes
/// nothing, never a guess; the winners stay bounded by the procedures
/// gathered, whatever the rows number.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `lines` - The winning rows, as [`Gathered::lines`] left them: their
///   offset in the image, the file's reference into the string table and
///   their line.
///
/// # Returns
///
/// Procedure RVA to the `(file, line)` its first row names.
pub(super) fn resolve_lines<'s>(
    db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
    lines: &BTreeMap<u32, (u32, pdb::StringRef, u32)>,
) -> BTreeMap<u32, (String, u32)> {
    let mut out = BTreeMap::new();
    if lines.is_empty() || !super::streams::names_table_ok(db) {
        return out;
    }
    let Ok(table) = db.string_table() else {
        return out;
    };
    for (start, (_, file, line)) in lines {
        let name = table.get(*file).map(|n| n.to_string()).unwrap_or_default();
        if !name.is_empty() {
            out.insert(*start, (crate::text::one_line(&name), *line));
        }
    }
    out
}
