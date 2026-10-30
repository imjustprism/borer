//! The key an index is stored under: the program's bytes, and everything
//! besides them that changes the text an index holds.

use std::fmt::Write as _;
use std::time::UNIX_EPOCH;

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::pack::Packs;
use borer_engine::program::Program;

use super::{FNV_SEED, FORMAT, IndexKey, fnv1a, program_key};

/// Returns the key an index for `program` is stored under.
///
/// That is the program's bytes, then the borer executable's size and
/// modification time, the file format, the packs the analysis ran with,
/// and what the load made of the bytes. The executable goes in because the text is what the decompiler of that
/// build renders; a newer borer must not read an older one's index. The
/// packs go in because they change the names the text uses. The load goes
/// in because one file loaded another way is another program: a raw load's
/// `arch`, `base` and `regions`, an `entry_file_offset`, and a companion
/// PDB applied or not move every address, name and type the text shows
/// while the bytes stay the same; it is the architecture, base, entry,
/// section table, symbols, function ranges, and the functions and types
/// debug information gave, hashed whole, since a PDB can name and type
/// what was already there without adding to any count. All are kept apart from the program's half, so a new index finds
/// and replaces the stale ones of its program by name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `packs` - The packs the analysis ran with.
#[must_use]
pub fn index_key(program: &Program, packs: &Packs) -> IndexKey {
    let mut h = fnv1a(FNV_SEED, &FORMAT.to_le_bytes());
    for pack in &packs.packs {
        for e in &pack.entries {
            for part in [&e.section, &e.key, &e.value] {
                h = fnv1a(h, part.as_bytes());
                h = fnv1a(h, &[0]);
            }
        }
        for (_, code) in &pack.scripts {
            h = fnv1a(h, code.as_bytes());
            h = fnv1a(h, &[0]);
        }
    }
    let mut load = Fnv(h);
    let _ = write!(
        load,
        "{:?} {:#x} {:?} {:?} {:?} {:?} {:?} {:?}",
        program.arch,
        program.image_base,
        program.entry,
        program.sections,
        program.symbols,
        program.function_ranges,
        program.debug_functions,
        program.debug_types
    );
    let mut h = load.0;
    if let Ok(exe) = std::env::current_exe()
        && let Ok(meta) = std::fs::metadata(exe)
    {
        h = fnv1a(h, &meta.len().to_le_bytes());
        let modified = meta
            .modified()
            .ok()
            .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
            .map_or(0, |d| d.as_secs());
        h = fnv1a(h, &modified.to_le_bytes());
    }
    IndexKey {
        program: program_key(&program.bytes),
        engine: h,
    }
}

/// An FNV-1a hash that text is written into a piece at a time, so a long
/// rendering is hashed without being built whole.
struct Fnv(u64);

impl std::fmt::Write for Fnv {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.0 = fnv1a(self.0, s.as_bytes());
        Ok(())
    }
}

/// The check, warning and next lines a `decompile` answer splices in.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `differs` - The repair search's note, when the text still differs.
///
/// # Returns
///
/// The lines without a final newline, or `None` when there are none.
pub fn answer_header(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    differs: Option<&str>,
) -> Option<String> {
    header_lines(program, analysis, overlay, entry, differs, None)
}

/// The check, warning and next lines, read from `body` when the caller
/// already rendered it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `differs` - The repair search's note, when the text still differs.
/// * `body` - The rendered text, or `None` to decompile it.
///
/// # Returns
///
/// The lines without a final newline, or `None` when there are none.
fn header_lines(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    differs: Option<&str>,
    body: Option<&str>,
) -> Option<String> {
    use borer_engine::analysis::{decompile, render};
    let mut lines: Vec<String> = decompile::checked_header(program, analysis, overlay, entry)
        .into_iter()
        .chain(
            analysis
                .incomplete
                .then(|| format!("//{}", render::INCOMPLETE_NOTE.trim_start_matches('#'))),
        )
        .collect();
    lines.extend(header_warnings(
        program, analysis, overlay, entry, differs, body,
    ));
    let steps = body.map_or_else(
        || render::next_steps(program, analysis, overlay, entry),
        |text| render::next_steps_for(program, analysis, overlay, entry, text),
    );
    lines.extend(steps.iter().map(|step| format!("// next: {step}")));
    (!lines.is_empty()).then(|| lines.join("\n"))
}

/// The `// warn:` line for `body`, decompiling when the caller has no text.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `differs` - The repair search's note, when the text still differs.
/// * `body` - The rendered text, or `None` to decompile it.
///
/// # Returns
///
/// The line, or `None` when nothing is known wrong.
fn header_warnings(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    differs: Option<&str>,
    body: Option<&str>,
) -> Option<String> {
    use borer_engine::analysis::decompile;
    match body {
        Some(text) => decompile::warnings(program, analysis, overlay, entry, text, differs),
        None => decompile::decompile_named(program, analysis, overlay, entry).and_then(|text| {
            decompile::warnings(program, analysis, overlay, entry, &text, differs)
        }),
    }
}

/// The text a `decompile` answer shows, so an index line is that line.
///
/// The warning and the next lines read `text`, which the index already
/// rendered, so this does not decompile the function again.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `text` - The body, or `None` when decompilation produced nothing.
///
/// # Returns
///
/// The body with its check, warning and next lines under the first line,
/// or empty when there is no body.
pub(super) fn shown(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: Option<String>,
) -> String {
    let Some(text) = text.filter(|body| !body.is_empty()) else {
        return String::new();
    };
    let header = header_lines(program, analysis, overlay, entry, None, Some(&text));
    borer_engine::analysis::decompile::with_header(&text, header.as_deref())
}
