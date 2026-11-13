//! PDB source-line resolution: picking each procedure's first line row and
//! naming its file from the string table.

use super::Gathered;
use std::collections::BTreeMap;
use std::io::Cursor;

/// Tracks module-stream uniqueness and line eligibility across [`super::gather`]'s DBI walk.
#[derive(Debug, Default)]
pub(super) struct LineReader {
    /// Per-module `(open_ok, sections)` gates aligned with `dbi.modules()`.
    gates: Vec<(bool, Option<super::streams::LineSections>)>,
    /// Index of the next module yielded by `dbi.modules()`.
    next: usize,
}

impl LineReader {
    /// Prepares module and line-program tracking for one [`super::gather`] pass.
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
        Self {
            gates: super::streams::module_gates(db, want),
            next: 0,
        }
    }

    /// Opens `m`'s module stream and reports its validated C13 line subsections.
    ///
    /// # Arguments
    ///
    /// * `db` - The opened PDB.
    /// * `m` - Next module yielded by `dbi.modules()`.
    ///
    /// # Returns
    ///
    /// The module's symbol and line stream paired with its validated C13
    /// `(section, offset)` headers when `line_program()` is wanted and within
    /// bounds, or `None` when `m` carries no unique readable stream.
    pub(super) fn open<'s>(
        &mut self,
        db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
        m: &pdb::Module<'_>,
    ) -> Option<(pdb::ModuleInfo<'s>, Option<super::streams::LineSections>)> {
        let idx = self.next;
        self.next += 1;
        let (open_ok, sections) = self
            .gates
            .get_mut(idx)
            .map_or((false, None), |(ok, s)| (*ok, s.take()));
        if !open_ok {
            return None;
        }
        let info = db.module_info(m).ok()??;
        Some((info, sections))
    }
}

impl Gathered {
    /// Reads `info`'s line program when `sections` is `Some` and records each procedure's first row.
    ///
    /// # Arguments
    ///
    /// * `info` - The module's symbol and line stream.
    /// * `sections` - Sorted `(section, offset)` headers of validated C13 line subsections.
    /// * `map` - Address map translating internal section offsets to RVAs.
    /// * `guard` - Checked RVA translation guard.
    /// * `procs` - Procedures sized in this module, `(rva, offset)`.
    pub(super) fn collect_module_lines(
        &mut self,
        info: &pdb::ModuleInfo<'_>,
        sections: Option<&[(u16, u32)]>,
        map: &pdb::AddressMap<'_>,
        guard: &super::streams::AddrGuard,
        procs: &[(u32, pdb::PdbInternalSectionOffset)],
    ) {
        if let Some(sections) = sections
            && !procs.is_empty()
            && let Ok(program) = info.line_program()
        {
            self.take_lines(&program, sections, map, guard, procs);
        }
    }

    /// Takes the first line row each stated procedure starts at.
    ///
    /// Each validated `DEBUG_S_LINES` subsection key in `sections` is queried
    /// once through `lines_for_symbol` so `pdb`'s iterator stays inside one
    /// subsection at a time while still reaching subsections that begin past a
    /// procedure's entry, before indexing rows by translated RVA.
    ///
    /// # Arguments
    ///
    /// * `program` - The module's line program.
    /// * `sections` - Sorted `(section, offset)` headers of C13 line subsections.
    /// * `map` - The address map, translating the internal offsets the
    ///   rows state into image RVAs.
    /// * `guard` - Checked RVA translation guard.
    /// * `procs` - Procedures sized in this module, `(rva, offset)`.
    fn take_lines(
        &mut self,
        program: &pdb::LineProgram<'_>,
        sections: &[(u16, u32)],
        map: &pdb::AddressMap<'_>,
        guard: &super::streams::AddrGuard,
        procs: &[(u32, pdb::PdbInternalSectionOffset)],
    ) {
        use pdb::FallibleIterator as _;
        if sections.is_empty() {
            return;
        }
        let mut lo = u32::MAX;
        let mut hi = 0u32;
        for &(rva, _) in procs {
            if let Some(&end) = self.extents.get(&rva)
                && rva < end
            {
                lo = lo.min(rva);
                hi = hi.max(end);
            }
        }
        if lo >= hi {
            return;
        }
        let mut by_rva: BTreeMap<u32, (pdb::StringRef, u32)> = BTreeMap::new();
        for &(section, offset) in sections {
            let mut rows =
                program.lines_for_symbol(pdb::PdbInternalSectionOffset { section, offset });
            while let Ok(Some(row)) = rows.next() {
                if row.line_start == 0 {
                    continue;
                }
                let Some(at) = guard.rva_of(map, row.offset) else {
                    continue;
                };
                if at < lo
                    || at >= hi
                    || by_rva
                        .get(&at)
                        .is_some_and(|&(_, best_line)| best_line <= row.line_start)
                {
                    continue;
                }
                if let Ok(file) = program.get_file_info(row.file_index) {
                    by_rva.insert(at, (file.name, row.line_start));
                }
            }
        }
        for &(rva, _) in procs {
            let Some(&end) = self.extents.get(&rva) else {
                continue;
            };
            let Some((&at, &(file, line))) = by_rva.range(rva..end).next() else {
                continue;
            };
            if !self
                .lines
                .get(&rva)
                .is_some_and(|&(best, _, best_line)| best < at || (best == at && best_line <= line))
            {
                self.lines.insert(rva, (at, file, line));
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
